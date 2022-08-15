
#include "math/sls/arith_sls.h"

namespace arith {


    sls::var_t sls::add_var(var_kind k, rational const& value) {
        var_t v = m_vars.size();
        m_vars.push_back({ value, value, k, {} });
        return v;
    }

    sls::atom_t sls::add_atom(vector<std::pair<rational, var_t>> const& args,
        ineq_kind op,
        rational const& bound) {
        atom_t a = m_atoms.size();
        rational arg_value(0);
        for (auto const& [coeff, v] : args) {
            arg_value += coeff * value(v);
            m_vars[v].m_atoms.push_back({coeff, a});
        }
        m_atoms.push_back({ {args, op, bound, arg_value}, (unsigned) - 1, false, true});
        return a;
    }

    void sls::undo_atoms(unsigned sz) {
        for (unsigned i = 0; i < sz; ++i) {
            auto const& ai = m_atoms.back();
            for (auto const & [coeff, v] : ai.m_ineq.m_args)
                m_vars[v].m_atoms.pop_back();
            m_atoms.pop_back();
        }
    }

    sls::atom_t sls::add_bool_atom(bool phase) {
        atom_t a = m_atoms.size();
        m_atoms.push_back({ {}, (unsigned)-1, true, phase });
        return a;
    }

    void sls::add_clause(svector<atom_t> const& arith, svector<sat::literal> const& bools) {
        unsigned clause_idx = m_clauses.size();        
        m_clauses.push_back({ bools, arith, 1, rational::zero() });
        clause& cl = m_clauses.back();
        cl.m_dts = dts(cl);
        for (sat::literal lit : bools) {
            m_use_list.reserve((1 + lit.var()) * 2);
            m_use_list[lit.index()].push_back(clause_idx);
            if (is_true(lit))
                cl.add(lit);
        }

        for (auto a : arith)
            m_atoms[a].m_clause_idx = clause_idx;

        if (!cl.is_true()) {
            m_best_min_unsat++;
            m_unsat.insert(clause_idx);
        }
        else if (cl.m_dts > 0 && cl.m_num_trues == 1) 
            inc_break(sat::to_literal(cl.m_trues));
        

        m_probs.reserve(bools.size());
    }

    void sls::auto_config() {
        unsigned max_len = 0;
        for (clause const& c : m_clauses) {
            max_len = std::max(max_len, c.m_bools.size());
        }
        // ProbSat magic constants
        switch (max_len) {
        case 0: case 1: case 2: case 3: m_config.cb = 2.5; break;
        case 4: m_config.cb = 2.85; break;
        case 5: m_config.cb = 3.7; break;
        case 6: m_config.cb = 5.1; break;
        default: m_config.cb = 5.4; break;
        }

        unsigned max_num_occ = 0;
        for (auto const& ul : m_use_list) {
            max_num_occ = std::max(max_num_occ, ul.size());
        }
        // vodoo from prob-sat
        m_prob_break.reserve(max_num_occ + 1);
        for (int i = 0; i <= static_cast<int>(max_num_occ); ++i) {
            m_prob_break[i] = pow(m_config.cb, -i);
        }
    }

    std::ostream& sls::display(std::ostream& out) const {
        unsigned i = 0;
        for (auto const& clause : m_clauses)
            display(out, clause);
        for (auto const& vi : m_vars)
            display(out, i++, vi);        
        return out;
    }

    std::ostream& sls::display(std::ostream& out, clause const& clause) const {
        out << (clause.is_true() ? "T":"F") << ": ";
        for (auto a : clause.m_arith) 
            display(out, m_atoms[a]);
        for (auto lit : clause.m_bools)
            out << lit << " ";
        return out << "\n";
    }

    std::ostream& sls::display(std::ostream& out, atom_info const& ai) const {
        for (auto const& [coeff, v] : ai.m_ineq.m_args)
            out << coeff << " * v" << v << " ";
        switch (ai.m_ineq.m_op) {
        case ineq_kind::EQ: out << "= "; break;
        case ineq_kind::LE: out << "<= "; break;
        case ineq_kind::LT: out << "< "; break;
        case ineq_kind::NE: out << "!= "; break;
        default: break;
        }
        out << ai.m_ineq.m_bound << " ";
        return out;
    }

    std::ostream& sls::display(std::ostream& out, unsigned i, var_info const& vi) const {
        return out << "v" << i << ": " << vi.m_value << "\n";
    }

    void sls::log() {
        if (m_stats.m_num_flips % 1000 == 0)
            IF_VERBOSE(20, verbose_stream() << "(sls " << m_stats.m_num_flips << " " << m_unsat.size() << ")\n");
    }

    void sls::collect_statistics(statistics& st) const {
    }

    lbool sls::check() {
        init();
        unsigned rounds = 0;
        while (m_limit.inc() && !m_unsat.empty() && rounds < 40) {
            IF_VERBOSE(20, verbose_stream() << "(sls " << m_stats.m_num_flips << " " << m_unsat.size() << " " << m_best_min_unsat << ")\n");
            setup_bounds();
            check_bool();
            check_arith();
            ++rounds;
        }
        IF_VERBOSE(2, verbose_stream() << "(sls " << m_stats.m_num_flips << " " << m_unsat.size() << " " << m_best_min_unsat << ")\n");
        DEBUG_CODE(well_formed(););
        if (m_unsat.empty())
            return l_true;
        return l_undef;
    }

    void sls::setup_bounds() {
        unsigned num_arith = 0, num_bool = 0;
        for (auto idx : m_unsat) {
            num_arith += m_clauses[idx].m_arith.size();
            num_bool += m_clauses[idx].m_bools.size();
        }
        unsigned num_lits = num_arith + num_bool;
        m_max_arith_steps = (m_config.L * num_arith) / num_lits;
        m_max_bool_steps = (m_config.L * num_bool) / num_lits;
    }

    void sls::check_bool() {
        m_num_steps = 0;
        unsigned best = m_unsat.size(); //  m_best_min_unsat;
        while (m_limit.inc() && m_best_min_unsat > 0 && m_num_steps < m_max_bool_steps) {
            if (!flip_bool())
                return;
            if (m_unsat.size() < best) {
                best = m_unsat.size();
                m_num_steps = 0;
            }
            if (m_unsat.size() < m_best_min_unsat) {
                save_best_values();
            }
            else 
                ++m_num_steps;
        }
    }

    unsigned sls::pick_bool_clause() {
        unsigned start = m_rand();
        for (unsigned i = m_unsat.size(); i-- > 0; ) {
            unsigned cls_idx = m_unsat.elem_at((start + i) % m_unsat.size());
            if (!m_clauses[cls_idx].m_bools.empty())
                return cls_idx;
        }
        return UINT_MAX;
    }

    sat::bool_var sls::pick_var() {
        unsigned cls_idx = pick_bool_clause();
        if (cls_idx == UINT_MAX)
            return sat::null_bool_var;
        double sum_prob = 0;
        unsigned i = 0;
        clause const& c = m_clauses[cls_idx];
        for (sat::literal lit : c.m_bools) {
            unsigned breaks = m_atoms[lit.var()].m_breaks;
            // std::cout << breaks << " " << m_prob_break.size() << "\n";
            if (breaks >= m_prob_break.size())
                std::cout << "too many breaks " << lit << " " << breaks << "\n";
            double prob = m_prob_break[breaks];
            m_probs[i++] = prob;
            sum_prob += prob;
        }
        double lim = sum_prob * ((double)m_rand() / m_rand.max_value());
        do {
            lim -= m_probs[--i];
        } while (lim >= 0 && i > 0);
        return c.m_bools[i].var();
    }

    bool sls::flip_bool() {
        ++m_stats.m_num_flips;
        sat::bool_var v = pick_var();
        if (v == sat::null_bool_var)
            return false;
        update_bool(v);
        log();
        return true;
    }

    void sls::update_bool(sat::bool_var v) {
        sat::literal lit = sat::literal(v, !m_atoms[v].m_phase);
        sat::literal nlit = ~lit;

        // std::cout << "flip " << lit << " " << m_unsat.size() << "\n";

        SASSERT(is_true(lit));
        SASSERT(lit.index() < m_use_list.size());
        SASSERT(m_use_list_index.size() == m_use_list.size() + 1);

        
        for (unsigned cls_idx : use_list(*this, lit)) {
            clause& ci = m_clauses[cls_idx];
            ci.del(lit);
            if (ci.m_dts == 0)
                continue;
            switch (ci.m_num_trues) {
            case 0:
                m_unsat.insert(cls_idx);
                dec_break(lit);
                break;
            case 1:
                inc_break(sat::to_literal(ci.m_trues));
                break;
            default:
                break;
            }
        }
        for (unsigned cls_idx : use_list(*this, nlit)) {
            clause& ci = m_clauses[cls_idx];
            if (ci.m_dts == 0) {
                ci.add(nlit);
                continue;
            }
            switch (ci.m_num_trues) {
            case 0:
                m_unsat.remove(cls_idx);
                inc_break(nlit);
                break;
            case 1:
                dec_break(sat::to_literal(ci.m_trues));
                break;
            default:
                break;
            }
            ci.add(nlit);
        }
        m_atoms[v].m_phase = !m_atoms[v].m_phase;
    }

    void sls::check_arith() {
        m_num_steps = 0;
        unsigned best = m_best_min_unsat;
        while (m_limit.inc() && m_best_min_unsat > 0 && m_num_steps < m_max_arith_steps) {
            unsigned prev = m_unsat.size();
            if (!flip_arith())
                return;
            if (m_unsat.size() < best) {
                best = m_unsat.size();
                m_num_steps = 0;
            }
            if (m_unsat.size() < m_best_min_unsat) 
                save_best_values();            
            else
                ++m_num_steps;
        }
    }

    bool sls::flip_arith() {
        ++m_stats.m_num_flips;
        log();
        if (flip_arith_unsat())
            return true;
        if (flip_arith_clauses())
            return true;
        if (flip_arith_dscore())
            return true;
        return false;
    }

    bool sls::flip_arith_unsat() {
        unsigned start = m_rand();
        for (unsigned i = m_unsat.size(); i-- > 0; ) {
            unsigned cl = m_unsat.elem_at((i + start) % m_unsat.size());
            if (flip_arith(m_clauses[cl]))
                return true;
        }
        return false;
    }

    bool sls::flip_arith_clauses() {
        unsigned start = m_rand();
        for (unsigned i = m_clauses.size(); i-- > 0; )
            if (flip_arith(m_clauses[(i + start) % m_clauses.size()]))
                return true;
        return false;
    }

    bool sls::flip_arith_dscore() {
        paws();
        unsigned start = m_rand();
        for (unsigned i = m_unsat.size(); i-- > 0; ) {
            unsigned cl = m_unsat.elem_at((i + start) % m_unsat.size());
            if (flip_arith_dscore(m_clauses[cl]))
                return true;
        }
        std::cout << "flip dscore\n";
        IF_VERBOSE(2, verbose_stream() << "(sls " << m_stats.m_num_flips << " " << m_unsat.size() << ")\n");
        return false;
    }

    bool sls::flip_arith_dscore(clause const& clause) {
        rational new_value, min_value, min_score(-1);
        var_t min_var = UINT_MAX;
        for (auto a : clause.m_arith) {
            auto const& ai = m_atoms[a];
            ineq const& ineq = ai.m_ineq;
            for (auto const& [coeff, v] : ineq.m_args) {
                if (!ineq.is_true() && cm(ineq, v, new_value)) {
                    rational score = dscore(v, new_value);
                    if (UINT_MAX == min_var || score < min_score) {
                        min_var = v;
                        min_value = new_value;
                        min_score = score;
                    }
                }
            }
        }
        if (min_var != UINT_MAX) {
            update(min_var, min_value);
            return true;
        }
        return false;
    }

    void sls::paws() {
        for (auto& clause : m_clauses) {
            bool above = 10000 * m_config.sp <= (m_rand() % 10000);
            if (!above && clause.is_true() && clause.m_weight > 1)
                clause.m_weight -= 1;
            if (above && !clause.is_true())
                clause.m_weight += 1;
        }
    }

    void sls::update(var_t v, rational const& new_value) {
        auto& vi = m_vars[v];
        auto const& old_value = vi.m_value;
        for (auto const& [coeff, atm] : vi.m_atoms) {
            auto& ai = m_atoms[atm];
            SASSERT(!ai.m_is_bool);
            auto& clause = m_clauses[ai.m_clause_idx];
            rational dtt_old = dtt(ai.m_ineq);
            ai.m_ineq.m_args_value += coeff * (new_value - old_value);
            rational dtt_new = dtt(ai.m_ineq);
            bool was_true = clause.is_true();
            if (dtt_new < clause.m_dts) {           
                if (was_true && clause.m_dts > 0 && dtt_new == 0 && 1 == clause.m_num_trues) {
                    for (auto lit : clause.m_bools) {
                        if (is_true(lit)) {
                            dec_break(lit);
                            break;
                        }
                    }
                }
                clause.m_dts = dtt_new;
                if (!was_true && clause.is_true())
                    m_unsat.remove(ai.m_clause_idx);
            }
            else if (clause.m_dts == dtt_old && dtt_old < dtt_new) {
                clause.m_dts = dts(clause);
                if (was_true && !clause.is_true())
                    m_unsat.insert(ai.m_clause_idx);
                if (was_true && clause.is_true() && clause.m_dts > 0 && dtt_old == 0 && 1 == clause.m_num_trues) {
                    for (auto lit : clause.m_bools) {
                        if (is_true(lit)) {
                            inc_break(lit);
                            break;
                        }
                    }
                }
            }
            SASSERT(clause.m_dts >= 0);
        }
        vi.m_value = new_value;
    }

    bool sls::flip_arith(clause const& clause) {
        rational new_value;
        for (auto a : clause.m_arith) {
            auto const& ai = m_atoms[a];
            ineq const& ineq = ai.m_ineq;
            for (auto const& [coeff, v] : ineq.m_args) {
                if (!ineq.is_true() && cm(ineq, v, new_value)) {
                    int score = cm_score(v, new_value);
                    if (score <= 0)
                        continue;
                    unsigned num_unsat = m_unsat.size();
                    update(v, new_value);
                    std::cout << "score " << v << " " << score << "\n";                    
                    std::cout << num_unsat << " -> " << m_unsat.size() << "\n";
                    return true;
                } 
            }
        }
        return false;
    }


    void sls::flatten_use_list() {
        m_use_list_index.reset();
        m_flat_use_list.reset();
        for (auto const& ul : m_use_list) {
            m_use_list_index.push_back(m_flat_use_list.size());
            m_flat_use_list.append(ul);
        }
        m_use_list_index.push_back(m_flat_use_list.size());
    }

    void sls::init() {
        flatten_use_list();
        //init_random_values();
        auto_config();
        save_best_values();
    }

    void sls::save_best_values() {
        for (auto& vi : m_vars)
            vi.m_best_value = vi.m_value;
        for (auto& ai : m_atoms)
            ai.m_best_phase = ai.m_is_bool ? ai.m_phase : ai.m_ineq.is_true();
        m_best_min_unsat = m_unsat.size();
        log();
    }

    void sls::well_formed() const {
        unsigned i = 0;
        for (auto const& clause : m_clauses) {
            well_formed(clause);
            SASSERT(clause.is_true() != m_unsat.contains(i));
            ++i;
        }
    }

    void sls::well_formed(clause const& clause) const {
        rational min_dtt = clause.m_dts + 1;
        bool has_arith = false;
        for (auto a : clause.m_arith) {
            atom_info const& ai = m_atoms[a];
            has_arith = true;
            rational adtt = dtt(ai.m_ineq);
            SASSERT(clause.m_dts <= adtt);
            if (adtt < min_dtt)
                min_dtt = adtt;
        }
        SASSERT(!has_arith || min_dtt == clause.m_dts);        
    }

    // distance to true
    rational sls::dtt(rational const& args, ineq const& ineq) const {
        switch (ineq.m_op) {
        case ineq_kind::LE:
            if (args <= ineq.m_bound)
                return rational::zero();
            return args - ineq.m_bound;
        case ineq_kind::EQ:
            if (args == ineq.m_bound)
                return rational::zero();            
            return rational::one();
        case ineq_kind::NE:
            if (args == ineq.m_bound)
                return rational::one();
            return rational::zero();
        case ineq_kind::LT:
        default:
            if (args < ineq.m_bound)
                return rational::zero();
            return args - ineq.m_bound + 1;
        }
    }

    rational sls::dtt(ineq const& ineq, var_t v, rational const& new_value) const {        
        auto new_args_value = ineq.m_args_value;
        for (auto const& [coeff, w] : ineq.m_args) {
            if (w == v) {
                new_args_value += coeff * (new_value - m_vars[w].m_value);
                break;
            }                
        }
        return dtt(new_args_value, ineq);
    }

    rational sls::dts(clause const& cl) const {
        rational d(1), d2;
        bool first = true;
        for (auto a : cl.m_arith) {
            auto const& ai = m_atoms[a];
            d2 = dtt(ai.m_ineq);
            if (first)
                d = d2, first = false;
            else
                d = std::min(d, d2);
            if (d == 0)
                break;
        }
        return d;
    }

    rational sls::dts(clause const& cl, var_t v, rational const& new_value) const {
        rational d(1), d2;
        bool first = true;
        for (auto a : cl.m_arith) {
            auto const& ai = m_atoms[a];
            d2 = dtt(ai.m_ineq, v, new_value);
            if (first)
                d = d2, first = false;
            else
                d = std::min(d, d2);
            if (d == 0)
                break;
        }
        return d;
    }

    //
    // dscore(op) = sum_c (dts(c,alpha) - dts(c,alpha_after)) * weight(c)
    // 
    rational sls::dscore(var_t v, rational const& new_value) const {
        auto const& vi = m_vars[v];
        rational score(0);
        for (auto const& [coeff, atm] : vi.m_atoms) {
            auto const& ai = m_atoms[atm];
            auto const& cl = m_clauses[ai.m_clause_idx];
            score += (cl.m_dts - dts(cl, v, new_value)) * rational(cl.m_weight); 
        }
        return score;
    }

    // critical move
    bool sls::cm(ineq const& ineq, var_t v, rational& new_value) {
        SASSERT(!ineq.is_true());
        auto delta = ineq.m_args_value - ineq.m_bound;
        for (auto const& [coeff, w] : ineq.m_args) {
            if (w == v) {
                if (coeff > 0) 
                    new_value = value(v) - abs(ceil(delta/coeff));
                else
                    new_value = value(v) + abs(floor(delta/coeff)); 
                switch (ineq.m_op) {
                case ineq_kind::LE:
                    SASSERT(delta + coeff * (new_value - value(v)) <= 0);
                    return true;
                case ineq_kind::EQ:
                    return delta + coeff * (new_value - value(v)) == 0;
                case ineq_kind::NE:
                    return delta + coeff * (new_value - value(v)) != 0;
                case ineq_kind::LT:
                    return delta + coeff*(new_value - value(v)) < 0;
                default:
                    UNREACHABLE(); break;
                }
            }
        }
        return false;
    }

    int sls::cm_score(var_t v, rational const& new_value) {
        int score = 0;
        auto& vi = m_vars[v];
        for (auto const& [coeff, atm] : vi.m_atoms) {
            auto const& ai = m_atoms[atm];
            auto const& clause = m_clauses[ai.m_clause_idx];
            rational dtt_old = dtt(ai.m_ineq);
            rational dtt_new = dtt(ai.m_ineq, v, new_value);
            if (!clause.is_true()) {
                if (dtt_new == 0)
                    ++score;
            }
            else if (dtt_new == 0 || dtt_old > 0 || clause.m_num_trues > 0)
                continue;
            else {
                bool has_true = false;
                for (auto a : clause.m_arith) {
                    auto const& ai = m_atoms[a];
                    rational d = dtt(ai.m_ineq, v, new_value);
                    has_true |= (d == 0);                        
                }
                if (!has_true)
                    --score;
            }
        }
        return score;
    }


}
