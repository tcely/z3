/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    arith_axioms.cpp

Abstract:

    Theory plugin for arithmetic

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-08

--*/

#include "sat/smt/euf_solver.h"
#include "sat/smt/arith_solver.h"
#include "math/sls/arith_sls.h"


namespace arith {

    void solver::simplify() {
        sls();
    }

    void solver::init_search() {
        sls();
    }

    void solver::sls() {
        arith::sls local_search;
        unsigned_vector bool_var2atom;

        for (sat::bool_var v = 0; v < s().num_vars(); ++v) 
            bool_var2atom.push_back(local_search.add_bool_atom(s().get_phase(v)));        

        vector<::std::pair<rational, sls::var_t>> args;
        sat::literal_vector lits;
        svector<sls::atom_t> arith;
        svector<std::pair<lp::tv, theory_var>> terms;
        svector<std::pair<sat::literal, sls::atom_t>> atoms;
        bool is_tautology = false;

        auto reset_state = [&]() {
            lits.reset();
            arith.reset();
            is_tautology = false;
        };

        auto add_args = [&](lp::tv t, theory_var v, rational sign) {
            if (t.is_term()) {
                terms.push_back({ t,v });
                lp::lar_term const& term = lp().get_term(t);

                for (lp::lar_term::ival arg : term) {
                    auto t2 = lp().column2tv(arg.column());
                    auto w = lp().local_to_external(t2.id());
                    args.push_back({ sign * arg.coeff(), w });
                }
            }
            else
                args.push_back({ sign, lp().local_to_external(t.id()) });
        };

        for (unsigned v = 0; v < get_num_vars(); ++v) {
            rational value = is_registered_var(v) ? get_ivalue(v).x : rational::zero();
            sls::var_t w = local_search.add_var(is_int(v) ? sls::var_kind::INT : sls::var_kind::REAL, is_int(v) ? ceil(value) : value);
            SASSERT(v == w);

            rational lo, hi;
            bool is_strict_lo = false, is_strict_hi = false;
            lp::constraint_index ci;
            if (!is_registered_var(v))
                continue;
            lp::column_index vi = lp().to_column_index(v);
            if (vi.is_null())
                continue;
            bool has_lo = lp().has_lower_bound(vi.index(), ci, lo, is_strict_lo);
            bool has_hi = lp().has_upper_bound(vi.index(), ci, hi, is_strict_hi);
            if (!has_lo && !has_hi)
                continue;

            if (has_lo && has_hi && lo == hi) {
                reset_state();
                args.reset();
                args.push_back({ rational::one(), v});
                sls::atom_t a = local_search.add_atom(args, sls::ineq_kind::EQ, lo);
                arith.push_back(a);
                local_search.add_clause(arith, lits);
                continue;
            }
            if (has_lo) {
                reset_state();
                args.reset();
                args.push_back({ -rational::one(), v});
                sls::atom_t a = local_search.add_atom(args, is_strict_lo ? sls::ineq_kind::LT : sls::ineq_kind::LE, -lo);
                arith.push_back(a);
                local_search.add_clause(arith, lits);
            }
            if (has_hi) {
                reset_state();
                args.reset();
                args.push_back({ rational::one(), v});
                sls::atom_t a = local_search.add_atom(args, is_strict_hi ? sls::ineq_kind::LT : sls::ineq_kind::LE, hi);
                arith.push_back(a);
                local_search.add_clause(arith, lits);
            }
        }


        auto literal2lit = [&](sat::literal lit, bool prune) {
            api_bound* b = nullptr;
            m_bool_var2bound.find(lit.var(), b);
            if (b) {
                auto t = b->tv();
                rational bound = b->get_value();
                sls::ineq_kind op;
                args.reset();
                add_args(t, b->get_var(), rational::one());

                if (!lit.sign()) {
                    if (b->get_bound_kind() == lp::GE) {
                        for (auto& a : args)
                            a.first.neg();
                        bound.neg();
                    }
                    op = sls::ineq_kind::LE;
                }
                else {
                    if (b->get_bound_kind() == lp::LE) {
                        for (auto& a : args)
                            a.first.neg();
                        bound.neg();
                    }
                    if (is_int(b->get_var())) {
                        bound -= 1;
                        op = sls::ineq_kind::LE;
                    }
                    else
                        op = sls::ineq_kind::LT;

                }
                sls::atom_t a = local_search.add_atom(args, op, bound);
                arith.push_back(a);
                atoms.push_back({ lit, a });
                return;
            }

            expr* e = bool_var2expr(lit.var());
            expr* l = nullptr, * r = nullptr;
            if (e && m.is_eq(e, l, r) && a.is_int(l)) {
                theory_var u = get_th_var(l);
                theory_var v = get_th_var(r);
                lp::tv tu = get_tv(u);
                lp::tv tv = get_tv(v);
                args.reset();
                add_args(tu, u, rational::one());
                add_args(tv, v, -rational::one());
                sls::atom_t a = local_search.add_atom(args, lit.sign() ? sls::ineq_kind::NE : sls::ineq_kind::EQ, rational::zero());
                arith.push_back(a); 
                atoms.push_back({ lit, a });
                return;
            }

            if (prune) {
                switch (s().value(lit)) {
                case l_true:
                    is_tautology = true;
                    return;
                case l_false:
                    return;
                default:
                    break;
                }
            }

            unsigned atm = bool_var2atom.get(lit.var(), sat::null_bool_var);
            lits.push_back(sat::literal(atm, lit.sign()));
        };

        auto add_clause = [&]() {
            if (is_tautology) {
                local_search.undo_atoms(arith.size());
                atoms.shrink(atoms.size() - arith.size());
            }
            else
                local_search.add_clause(arith, lits);
        };

        auto const& clauses = s().clauses();
        typedef std::pair<literal, literal> bin_clause;
        svector<bin_clause> bin_clauses;
        s().collect_bin_clauses(bin_clauses, false, false);

        for (sat::bool_var v = 0; v < s().num_vars(); ++v) {
            lbool val = s().value(v);
            if (val != l_undef) {
               reset_state();
               literal2lit(sat::literal(v, val == l_false), false);
               local_search.add_clause(arith, lits);
            }
        }
        for (auto const& [a, b] : bin_clauses) {
            reset_state();
            literal2lit(a, true);
            literal2lit(b, true);
            add_clause();                
        }
        for (auto* cl : clauses) {
            reset_state();
            for (sat::literal lit : *cl)
                literal2lit(lit, true);
            add_clause();
        }

        lbool is_sat = local_search.check();
        std::cout << is_sat << "\n";
        for (sat::bool_var v = 0; v < s().num_vars(); ++v) {
            sat::literal lit(v, !local_search.best_phase(v));
            s().set_phase(lit);
        }
        for (auto const& [lit, a] : atoms) 
            s().set_phase(local_search.best_phase(a) ? lit : ~lit);        

        // first compute assignment to terms
        // then update non-basic variables in tableau, assuming a sat solution was found.
        for (auto const& [t,v] : terms) {
            rational val;
            lp::lar_term const& term = lp().get_term(t);
            for (lp::lar_term::ival arg : term) {
                auto t2 = lp().column2tv(arg.column());
                auto w = lp().local_to_external(t2.id());
                val += arg.coeff() * local_search.value(w);
            }
            local_search.update(v, val);
        }

        
        for (unsigned v = 0; is_sat == l_true && v < get_num_vars(); ++v) {
            if (is_bool(v))
                continue;
            if (!lp().external_is_used(v))
                continue;
            rational value = is_registered_var(v) ? get_ivalue(v).x : rational::zero();
            rational new_value = local_search.value(v);
            if (value == new_value)
                continue;
            ensure_column(v);
            lp::column_index vj = lp().to_column_index(v);
            SASSERT(!vj.is_null());
            if (!lp().is_base(vj.index())) {
                lp::impq val(new_value);
                lp().set_value_for_nbasic_column(vj.index(), val);
            }
        }       
    }
}
