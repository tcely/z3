
#pragma once

#include "util/rational.h"
#include "util/vector.h"
#include "util/rlimit.h"
#include "util/uint_set.h"
#include "util/lbool.h"
#include "util/statistics.h"
#include "util/sat_literal.h"

namespace arith {
    class sls {
    public:
        enum class ineq_kind { EQ, LE, LT, NE };
        enum class var_kind { INT, REAL };
        typedef unsigned var_t;
        typedef unsigned atom_t;

    protected:
        struct config {
            double cb = 0.0;
            unsigned L = 20;
            unsigned t = 45;
            unsigned max_no_improve = 500000;
            double sp = 0.0003;
        };

        struct stats {
            unsigned m_num_flips = 0;
        };


        // encode args <= bound, args = bound, args < bound
        struct ineq {
            vector<std::pair<rational, var_t>> m_args;
            ineq_kind  m_op = ineq_kind::LE;
            rational   m_bound;
            rational   m_args_value;

            bool is_true() const {
                switch (m_op) {
                case ineq_kind::LE:
                    return m_args_value <= m_bound;
                case ineq_kind::EQ:
                    return m_args_value == m_bound;
                case ineq_kind::NE:
                    return m_args_value != m_bound;
                default:
                    return m_args_value < m_bound;
                }
            }
        };

        struct clause {
            svector<sat::literal> m_bools;
            svector<atom_t> m_arith;
            unsigned m_weight = 1;
            rational m_dts = rational::one();
            unsigned m_num_trues = 0;
            unsigned m_trues = 0;
            void add(sat::literal lit) { ++m_num_trues; m_trues += lit.index(); }
            void del(sat::literal lit) { SASSERT(m_num_trues > 0); --m_num_trues; m_trues -= lit.index(); }
            bool is_true() const { return m_dts.is_zero() || m_trues > 0; }
        };

        struct var_info {
            rational     m_value;
            rational     m_best_value;
            var_kind     m_kind = var_kind::INT;
            vector<std::pair<rational, atom_t>> m_atoms;
        };

        struct atom_info {
            ineq            m_ineq;
            unsigned        m_clause_idx;
            bool            m_is_bool = false;
            bool            m_phase = false;
            bool            m_best_phase = false;
            unsigned        m_breaks = 0;
        };


        // var_t -> (coeff * atom)-set  - where do variables occur
        // atom -> clause-set           - clauses containing atom
        // atom -> lhs_value            - value of args
        // atom -> ineq
        // clause -> num_true, weight

        config               m_config;
        stats                m_stats;
        reslimit             m_limit;
        vector<atom_info>    m_atoms;
        vector<var_info>     m_vars;     
        vector<clause>       m_clauses;

        random_gen           m_rand;
        indexed_uint_set     m_unsat;
        unsigned             m_best_min_unsat = std::numeric_limits<unsigned>::max();
        unsigned             m_max_bool_steps = std::numeric_limits<unsigned>::max();
        unsigned             m_max_arith_steps = std::numeric_limits<unsigned>::max();
        unsigned             m_num_steps = 0;

        vector<unsigned_vector> m_use_list;
        unsigned_vector  m_flat_use_list;
        unsigned_vector  m_use_list_index;
        svector<double>  m_probs, m_prob_break;

        void paws();

        void init();

        void auto_config();

        rational dscore(var_t v, rational const& new_value) const;

        sat::bool_var pick_var();

        unsigned pick_bool_clause();

        bool flip_bool();

        void save_best_values();

        bool flip_arith();

        bool flip_arith_unsat();

        bool flip_arith_clauses();

        bool flip_arith_dscore();

        bool flip_arith_dscore(clause const&);

        bool flip_arith(clause const&);

        rational dtt(ineq const& ineq) const { return dtt(ineq.m_args_value, ineq); }

        rational dtt(rational const& args, ineq const& ineq) const;

        rational dtt(ineq const& ineq, var_t v, rational const& new_value) const;

        rational dts(clause const& cl, var_t v, rational const& new_value) const;

        rational dts(clause const& cl) const;

        bool cm(ineq const& ineq, var_t v, rational& new_value);

        int cm_score(var_t v, rational const& new_value);

        void update_bool(sat::bool_var v);

        std::ostream& display(std::ostream& out, atom_info const& ai) const;

        std::ostream& display(std::ostream& out, clause const& clause) const;

        std::ostream& display(std::ostream& out, unsigned i, var_info const& vi) const;

        void well_formed() const;

        void well_formed(clause const& clause) const;

        void log();

        inline void inc_break(sat::literal lit) { m_atoms[lit.var()].m_breaks++; }

        inline void dec_break(sat::literal lit) { m_atoms[lit.var()].m_breaks--; }

        bool is_true(sat::literal lit) const { return m_atoms[lit.var()].m_phase != lit.sign(); }

        void setup_bounds();

        class use_list {
            sls& p;
            unsigned i;
        public:
            use_list(sls& p, sat::literal lit) :
                p(p), i(lit.index()) {}
            unsigned const* begin() { return p.m_flat_use_list.data() + p.m_use_list_index[i]; }
            unsigned const* end() { return p.m_flat_use_list.data() + p.m_use_list_index[i + 1]; }
        };

        void flatten_use_list();

        void check_bool();

        void check_arith();


    public:

        var_t add_var(var_kind k, rational const& value);
        
        atom_t add_atom(vector<std::pair<rational, var_t>> const& args,
                        ineq_kind op,
                        rational const& bound); 

        atom_t add_bool_atom(bool phase);

        void add_clause(svector<atom_t> const& arith, svector<sat::literal> const& bools);

        lbool check();

        void update(var_t v, rational const& new_value);

        rational value(var_t v) const { return m_vars[v].m_value; }

        rational best_value(var_t v) const { return m_vars[v].m_best_value; }

        bool best_phase(atom_t v) const { return m_atoms[v].m_best_phase; }

        std::ostream& display(std::ostream& out) const;

        void collect_statistics(statistics& st) const;

        void undo_atoms(unsigned sz);
        
    };
}
