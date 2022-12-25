/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Polysat core saturation

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6


TODO: preserve falsification
- each rule selects a certain premises that are problematic.
  If the problematic premise is false under the current assignment, the newly inferred
  literal should also be false in the assignment in order to preserve conflicts.


TODO: when we check that 'x' is "unary":
- in principle, 'x' could be any polynomial. However, we need to divide the lhs by x, and we don't have general polynomial division yet.
  so for now we just allow the form 'value*variable'.
   (extension to arbitrary monomials for 'x' should be fairly easy too)

--*/
#include "math/polysat/saturation.h"
#include "math/polysat/solver.h"
#include "math/polysat/log.h"
#include "math/polysat/umul_ovfl_constraint.h"

namespace polysat {

    saturation::saturation(solver& s) : s(s), m_lemma(s) {}

    void saturation::log_lemma(pvar v, conflict& core) {
        IF_VERBOSE(1, auto const& cl = core.lemmas().back(); 
                   verbose_stream() << m_rule << " v" << v << " "; 
                   for (auto lit : *cl) verbose_stream() << s.lit2cnstr(lit) << " "; 
                   verbose_stream() << " " << *cl << "\n");
    }

    void saturation::perform(pvar v, conflict& core) {
        IF_VERBOSE(2, verbose_stream() << "v" << v << " " << core << "\n");
        for (auto c : core) 
            if (perform(v, c, core))
                return;
    }

    bool saturation::perform(pvar v, signed_constraint const& c, conflict& core) {
        if (c.is_currently_true(s))
            return false;

        if (c->is_ule()) {
            auto i = inequality::from_ule(c);
            return try_inequality(v, i, core);
        }
        if (c->is_umul_ovfl()) 
            return try_umul_ovfl(v, c, core);
        return false;
    }

    bool saturation::try_inequality(pvar v, inequality const& i, conflict& core) {
        bool prop = false;
        if (try_mul_bounds(v, core, i))
            prop = true;
        if (try_parity(v, core, i))
            prop = true;
        if (try_parity_diseq(v, core, i))
            prop = true;
        if (try_transitivity(v, core, i))
            prop = true;
        if (try_factor_equality(v, core, i))
            prop = true;
        if (try_infer_equality(v, core, i))
            prop = true;
        if (try_add_overflow_bound(v, core, i))
            prop = true;
        if (try_add_mul_bound(v, core, i))
            prop = true;
        if (try_mul_eq_bound(v, core, i))
            prop = true;
        if (try_ugt_x(v, core, i))
            prop = true;
        if (try_ugt_y(v, core, i))
            prop = true;
        if (try_ugt_z(v, core, i))
            prop = true;
        if (try_y_l_ax_and_x_l_z(v, core, i))            
            prop = true;
        if (false && try_tangent(v, core, i))
            prop = true;
        return prop;
    }

    bool saturation::try_umul_ovfl(pvar v, signed_constraint const& c, conflict& core) {
#if 1
        return false;
#else
        SASSERT(c->is_umul_ovfl());
        bool prop = false;
        if (c.is_positive()) {
            prop = try_umul_ovfl_bounds(v, c, core);
        }
        else {
            prop = try_umul_noovfl_bounds(v, c, core);
            if (false && try_umul_noovfl_lo(v, c, core))
                prop = true;
        }
        return prop;
#endif
    }

    bool saturation::try_umul_noovfl_lo(pvar v, signed_constraint const& c, conflict& core) {
        set_rule("[x] ~ovfl(x, y) => y = 0 or x <= x * y");
        SASSERT(c->is_umul_ovfl());
        if (!c.is_negative())
            return false;
        auto const& ovfl = c->to_umul_ovfl();
        auto V = s.var(v);
        auto p = ovfl.p(), q = ovfl.q();
        // TODO could relax condition to be that V occurs in p
        if (q == V) 
            std::swap(p, q);
        signed_constraint q_eq_0;
        if (p == V && is_forced_diseq(q, 0, q_eq_0)) {
            // ~ovfl(V,q) => q = 0 or V <= V*q
            m_lemma.reset();
            m_lemma.insert_eval(q_eq_0);
            if (propagate(v, core, c, s.ule(p, p * q)))
                return true;
        }
        return false;
    }

    /**
     * ~ovfl(p, q) & p >= k => q < 2^N/k
     * TODO: subusmed by narrowing inferences?
     */
    bool saturation::try_umul_noovfl_bounds(pvar x, signed_constraint const& c, conflict& core) {
        set_rule("[x] ~ovfl(x, q) & x >= k => q <= (2^N-1)/k");
        SASSERT(c->is_umul_ovfl());
        SASSERT(c.is_negative());
        auto const& ovfl = c->to_umul_ovfl();        
        auto p = ovfl.p(), q = ovfl.q();
        auto X = s.var(x);
        auto& m = p.manager();
        rational p_val, q_val;
        if (q == X) 
            std::swap(p, q);
        if (p == X) {
            vector<signed_constraint> x_ge_bound;
            if (!s.try_eval(q, q_val))
                return false;
            if (!has_lower_bound(x, core, p_val, x_ge_bound))
                return false;
            if (p_val * q_val <= m.max_value())
                return false;
            m_lemma.reset();
            m_lemma.insert_eval(~s.uge(X, p_val));
            signed_constraint conseq = s.ule(q, floor(m.max_value()/p_val));
            return propagate(x, core, c, conseq);
        }
        if (!s.try_eval(p, p_val) || !s.try_eval(q, q_val))
            return false;
        if (p_val * q_val <= m.max_value())
            return false;
        m_lemma.reset();
        m_lemma.insert_eval(~s.uge(q, q_val));
        signed_constraint conseq = s.ule(p, floor(m.max_value()/q_val));
        return propagate(x, core, c, conseq);
    }

   /**
    * ovfl(p, q) & p <= k => q > 2^N/k
    */
    bool saturation::try_umul_ovfl_bounds(pvar v, signed_constraint const& c, conflict& core) {
        SASSERT(c->is_umul_ovfl());
        SASSERT(c.is_positive());
        auto const& ovfl = c->to_umul_ovfl();
        auto p = ovfl.p(), q = ovfl.q();
        rational p_val, q_val;
        return false;
    }

    signed_constraint saturation::ineq(bool is_strict, pdd const& lhs, pdd const& rhs) {
        if (is_strict)
            return s.ult(lhs, rhs);
        else
            return s.ule(lhs, rhs);
    }

    bool saturation::propagate(pvar v, conflict& core, inequality const& crit, signed_constraint c) {
        return propagate(v, core, crit.as_signed_constraint(), c);
    }

    bool saturation::propagate(pvar v, conflict& core, signed_constraint const& crit, signed_constraint c) {
        if (is_forced_true(c))
            return false;

        // NSB - review is it enough to propagate a new literal even if it is not false?
        // unit propagation does not require conflicts.
        // it should just avoid redundant propagation on literals that are true
        //
        // Furthermore propagation cannot be used when the resolved variable comes from 
        // forbidden interval conflicts. The propagated literal effectively adds a new and simpler bound
        // on the non-viable variable. This bound then enables tighter non-viability conflicts.
        // Effectively c is forced false, but it is forced false within the context of constraints used for viability.
        //
        // The effective level of the propagation is the level of all the other literals. If their level is below the
        // last decision level (conflict level) we expect the propagation to be useful.
        // The current assumptions on how conflict lemmas are used do not accomodate propagation it seems.
        //

        m_lemma.insert(~crit);

        SASSERT(all_of(m_lemma, [this](sat::literal lit) { return is_forced_false(s.lit2cnstr(lit)); }));

        m_lemma.insert(c);
        core.add_lemma(m_rule, m_lemma.build());
        log_lemma(v, core);
        return true;
    }

    bool saturation::add_conflict(pvar v, conflict& core, inequality const& crit1, signed_constraint c) {
        return add_conflict(v, core, crit1, crit1, c);
    }

    bool saturation::add_conflict(pvar v, conflict& core, inequality const& _crit1, inequality const& _crit2, signed_constraint const c) {
        auto crit1 = _crit1.as_signed_constraint();
        auto crit2 = _crit2.as_signed_constraint();
        m_lemma.insert(~crit1);
        if (crit1 != crit2)
            m_lemma.insert(~crit2);

        LOG("critical " << m_rule << " " << crit1);
        LOG("consequent " << c << " value: " << c.bvalue(s) << " is-false: " << c.is_currently_false(s));

        SASSERT(all_of(m_lemma, [this](sat::literal lit) { return s.m_bvars.value(lit) == l_false; }));

        // Ensure lemma is a conflict lemma
        if (!is_forced_false(c)) 
            return false;

        // Constraint c is already on the search stack, so the lemma will not derive anything new.
        if (c.bvalue(s) == l_true)
            return false;

        m_lemma.insert_eval(c);
        core.add_lemma(m_rule, m_lemma.build());
        log_lemma(v, core);
        return true;
    }

    bool saturation::is_non_overflow(pdd const& x, pdd const& y, signed_constraint& c) {
        
        if (is_non_overflow(x, y)) {
            c = ~s.umul_ovfl(x, y);
            return true;
        }

        // TODO: do we really search the stack or can we just create the literal s.umul_ovfl(x, y)
        // and check if it is assigned, or not even create the literal but look up whether it is assigned?
        // constraint_manager uses m_dedup, alloc
        // but to probe whether a literal occurs these are not needed.
        // m_dedup.constraints.contains(&c);
        
        for (auto si : s.m_search) {
            if (!si.is_boolean())
                continue;
            if (si.is_resolved())
                continue;
            auto d = s.lit2cnstr(si.lit());
            if (!d->is_umul_ovfl() || !d.is_negative())
                continue;
            auto const& ovfl = d->to_umul_ovfl();
            if (x != ovfl.p() && x != ovfl.q())
                continue;
            if (y != ovfl.p() && y != ovfl.q())
                continue;
            c = d;
            return true;
        }
        return false;
    }

    /*
     * Match [v] .. <= v
     */
    bool saturation::is_l_v(pvar v, inequality const& i) {
        return i.rhs() == s.var(v);
    }

    /*
     * Match [v] v <= ...
     */
    bool saturation::is_g_v(pvar v, inequality const& i) {
        return i.lhs() == s.var(v);
    }

    /*
     * Match [x] x <= y
     */
    bool saturation::is_x_l_Y(pvar x, inequality const& i, pdd& y) {
        y = i.rhs();
        return is_g_v(x, i);
    }

    /*
     * Match [x] y <= x
     */
    bool saturation::is_Y_l_x(pvar x, inequality const& i, pdd& y) {
        y = i.lhs();
        return is_l_v(x, i);
    }

    /*
     * Match [x] y <= a*x
     */
    bool saturation::is_Y_l_Ax(pvar x, inequality const& i, pdd& a, pdd& y) {
        y = i.lhs();
        return is_xY(x, i.rhs(), a);
    }

    bool saturation::verify_Y_l_Ax(pvar x, inequality const& i, pdd const& a, pdd const& y) {
        return i.lhs() == y && i.rhs() == a * s.var(x);
    }

    /**
     * Match [x] a*x <= y
     */
    bool saturation::is_Ax_l_Y(pvar x, inequality const& i, pdd& a, pdd& y) {
        y = i.rhs();
        return is_xY(x, i.lhs(), a);
    }

    bool saturation::verify_Ax_l_Y(pvar x, inequality const& i, pdd const& a, pdd const& y) {
        return i.rhs() == y && i.lhs() == a * s.var(x);
    }

    /**
     * Match [x] a*x + b <= y
     */
    bool saturation::is_AxB_l_Y(pvar x, inequality const& i, pdd& a, pdd& b, pdd& y) {
        y = i.rhs();
        return i.lhs().degree(x) == 1 && (i.lhs().factor(x, 1, a, b), true);
    }

    bool saturation::verify_AxB_l_Y(pvar x, inequality const& i, pdd const& a, pdd const& b, pdd const& y) {
        return i.rhs() == y && i.lhs() == a * s.var(x) + b;
    }


    bool saturation::is_Y_l_AxB(pvar x, inequality const& i, pdd& y, pdd& a, pdd& b) {
        y = i.lhs();
        return i.rhs().degree(x) == 1 && (i.rhs().factor(x, 1, a, b), true);        
    }
    
    bool saturation::verify_Y_l_AxB(pvar x, inequality const& i, pdd const& y, pdd const& a, pdd& b) {
        return i.lhs() == y && i.rhs() == a * s.var(x) + b;
    }


    /**
     * Match [x] a*x + b <= y, val(y) = 0
     */
    bool saturation::is_AxB_eq_0(pvar x, inequality const& i, pdd& a, pdd& b, pdd& y) {
        y = i.rhs();
        rational y_val;
        if (!s.try_eval(y, y_val) || y_val != 0)
            return false;
        return i.lhs().degree(x) == 1 && (i.lhs().factor(x, 1, a, b), true);
    }

    bool saturation::verify_AxB_eq_0(pvar x, inequality const& i, pdd const& a, pdd const& b, pdd const& y) {
        return y.is_val() && y.val() == 0 && i.rhs() == y && i.lhs() == a * s.var(x) + b;
    }

    bool saturation::is_AxB_diseq_0(pvar x, inequality const& i, pdd& a, pdd& b, pdd& y) {
        if (!i.is_strict())
            return false;
        y = i.lhs();
        rational y_val;
        if (!s.try_eval(y, y_val) || y_val != 0)
            return false;
        return i.rhs().degree(x) == 1 && (i.rhs().factor(x, 1, a, b), true);
    }

    /**
     * Match [coeff*x] coeff*x*Y where x is a variable
     */
    bool saturation::is_coeffxY(pdd const& x, pdd const& p, pdd& y) {
        pdd xy = x.manager().zero();
        return x.is_unary() && p.try_div(x.hi().val(), xy) && xy.factor(x.var(), 1, y);
    }

    /**
     * Determine whether values of x * y is non-overflowing.
     */
    bool saturation::is_non_overflow(pdd const& x, pdd const& y) {
        rational x_val, y_val;
        rational bound = x.manager().two_to_N();
        return s.try_eval(x, x_val) && s.try_eval(y, y_val) && x_val * y_val < bound;
    }

    /**
     * Match [v] v*x <= z*x with x a variable
     */
    bool saturation::is_Xy_l_XZ(pvar v, inequality const& i, pdd& x, pdd& z) {
        return is_xY(v, i.lhs(), x) && is_coeffxY(x, i.rhs(), z);
    }

    bool saturation::verify_Xy_l_XZ(pvar v, inequality const& i, pdd const& x, pdd const& z) {
        return i.lhs() == s.var(v) * x && i.rhs() == z * x;
    }

    /**
     * Match [z] yx <= zx with x a variable
     */
    bool saturation::is_YX_l_zX(pvar z, inequality const& c, pdd& x, pdd& y) {
        return is_xY(z, c.rhs(), x) && is_coeffxY(x, c.lhs(), y);
    }

    bool saturation::verify_YX_l_zX(pvar z, inequality const& c, pdd const& x, pdd const& y) {
        return c.lhs() == y * x && c.rhs() == s.var(z) * x;
    }

    /**
     * Match [x] xY <= xZ
     */
    bool saturation::is_xY_l_xZ(pvar x, inequality const& c, pdd& y, pdd& z) {
        return is_xY(x, c.lhs(), y) && is_xY(x, c.rhs(), z);
    }

    /**
     * Match xy = x * Y
     */
    bool saturation::is_xY(pvar x, pdd const& xy, pdd& y) {
        return xy.degree(x) == 1 && xy.factor(x, 1, y);
    }

    // 
    // overall comment: we use value propagation to check if p is val
    // but we could also use literal propagation and establish there is a literal p = 0 that is true.
    // in this way the value of p doesn't have to be fixed.
    // 
    // is_forced_diseq already creates a literal.
    // is_non_overflow also creates a literal
    // 
    // The condition that p = val may be indirect.
    // it could be a literal
    // it could be by propagation of literals
    // Example:
    //  -35: v90 + v89*v43 + -1*v87 != 0     [ l_false bprop@0 pwatched ]
    //   36: ovfl*(v43, v89)                 [ l_false bprop@0 pwatched ]
    // -218: v90 + -1*v87 + -1 != 0          [ l_false eval@6 pwatched ]
    // 
    // what should we "pay" to establish this condition?
    // or do we just afford us to add this lemma?
    // 

    bool saturation::is_forced_eq(pdd const& p, rational const& val) {
        rational pv;
        if (s.try_eval(p, pv) && pv == val)
            return true;
        return false;
    }

    bool saturation::is_forced_diseq(pdd const& p, int i, signed_constraint& c) {
        c = s.eq(p, i);
        return is_forced_false(c);
    }

    bool saturation::is_forced_odd(pdd const& p, signed_constraint& c) {
        c = s.odd(p);
        return is_forced_true(c);
    }

    bool saturation::is_forced_false(signed_constraint const& c) {
        return c.bvalue(s) == l_false || c.is_currently_false(s);
    }

    bool saturation::is_forced_true(signed_constraint const& c) {
        return c.bvalue(s) == l_true || c.is_currently_true(s);
    }

    /**
     * Implement the inferences
     *  [x] yx < zx   ==>  Ω*(x,y) \/ y < z
     *  [x] yx <= zx  ==>  Ω*(x,y) \/ y <= z \/ x = 0
     */
    bool saturation::try_ugt_x(pvar v, conflict& core, inequality const& xy_l_xz) {
        set_rule("[x] yx <= zx");
        pdd x = s.var(v);
        pdd y = x;
        pdd z = x;
        signed_constraint non_ovfl;

        if (!is_xY_l_xZ(v, xy_l_xz, y, z))
            return false;
        if (!xy_l_xz.is_strict() && s.is_assigned(v) && s.get_value(v).is_zero())
            return false;
        if (!is_non_overflow(x, y, non_ovfl))
            return false;
        m_lemma.reset();
        m_lemma.insert_eval(~non_ovfl);
        if (!xy_l_xz.is_strict())
            m_lemma.insert_eval(s.eq(x));
        return add_conflict(v, core, xy_l_xz, ineq(xy_l_xz.is_strict(), y, z));
    }

    /**
     * [y] z' <= y /\ yx <= zx  ==>  Ω*(x,y) \/ z'x <= zx
     * [y] z' <= y /\ yx < zx   ==>  Ω*(x,y) \/ z'x < zx
     * [y] z' < y  /\ yx <= zx  ==>  Ω*(x,y) \/ z'x < zx
     * [y] z' < y  /\ yx < zx   ==>  Ω*(x,y) \/ z'x < zx       TODO: could strengthen the conclusion to z'x + 1 < zx
     */
    bool saturation::try_ugt_y(pvar v, conflict& core, inequality const& yx_l_zx) {
        set_rule("[y] z' <= y & yx <= zx");
        auto& m = s.var2pdd(v);
        pdd x = m.zero();
        pdd z = m.zero();
        if (!is_Xy_l_XZ(v, yx_l_zx, x, z))
            return false;
        for (auto si : s.m_search) {
            if (!si.is_boolean())
                continue;
            if (si.is_resolved())
                continue;
            auto d = s.lit2cnstr(si.lit());
            if (!d->is_ule())
                continue;
            auto l_y = inequality::from_ule(d);
            if (is_l_v(v, l_y) && try_ugt_y(v, core, l_y, yx_l_zx, x, z))
                return true;
        }
        return false;
    }

    bool saturation::try_ugt_y(pvar v, conflict& core, inequality const& l_y, inequality const& yx_l_zx, pdd const& x, pdd const& z) {
        SASSERT(is_l_v(v, l_y));
        SASSERT(verify_Xy_l_XZ(v, yx_l_zx, x, z));
        pdd const y = s.var(v);
        signed_constraint non_ovfl;
        if (!is_non_overflow(x, y, non_ovfl))
            return false;
        pdd const& z_prime = l_y.lhs();
        m_lemma.reset();
        m_lemma.insert_eval(~non_ovfl);
        return add_conflict(v, core, l_y, yx_l_zx, ineq(yx_l_zx.is_strict() || l_y.is_strict(), z_prime * x, z * x));
    }

    /**
     * [z] z <= y' /\ yx <= zx  ==>  Ω*(x,y') \/ yx <= y'x
     * [z] z <= y' /\ yx < zx   ==>  Ω*(x,y') \/ yx < y'x
     * [z] z < y'  /\ yx <= zx  ==>  Ω*(x,y') \/ yx < y'x
     * [z] z < y'  /\ yx < zx   ==>  Ω*(x,y') \/ yx < y'x       TODO: could strengthen the conclusion to yx + 1 < y'x
     */
    bool saturation::try_ugt_z(pvar z, conflict& core, inequality const& yx_l_zx) {
        set_rule("[z] z <= y' && yx <= zx");
        auto& m = s.var2pdd(z);
        pdd y = m.zero();
        pdd x = m.zero();
        if (!is_YX_l_zX(z, yx_l_zx, x, y))
            return false;
        for (auto si : s.m_search) {
            if (!si.is_boolean())
                continue;
            if (si.is_resolved())
                continue;
            auto d = s.lit2cnstr(si.lit());
            if (!d->is_ule())
                continue;
            auto z_l_y = inequality::from_ule(d);
            if (is_g_v(z, z_l_y) && try_ugt_z(z, core, z_l_y, yx_l_zx, x, y))
                return true;
        }
        return false;
    }

    bool saturation::try_ugt_z(pvar z, conflict& core, inequality const& z_l_y, inequality const& yx_l_zx, pdd const& x, pdd const& y) {
        SASSERT(is_g_v(z, z_l_y));
        SASSERT(verify_YX_l_zX(z, yx_l_zx, x, y));
        pdd const& y_prime = z_l_y.rhs();
        signed_constraint non_ovfl;
        if (!is_non_overflow(x, y_prime, non_ovfl))
            return false;
        m_lemma.reset();
        m_lemma.insert_eval(~non_ovfl);
        return add_conflict(z, core, yx_l_zx, z_l_y, ineq(z_l_y.is_strict() || yx_l_zx.is_strict(), y * x, y_prime * x));
    }

    /**
     * [x]  y <= ax /\ x <= z  (non-overflow case)
     *     ==>   Ω*(a, z)  \/  y <= az
     * ... (other combinations of <, <=)
     */
    bool saturation::try_y_l_ax_and_x_l_z(pvar x, conflict& core, inequality const& y_l_ax) {
        set_rule("[x] y <= ax & x <= z");
        auto& m = s.var2pdd(x);
        pdd y = m.zero();
        pdd a = m.zero();
        if (!is_Y_l_Ax(x, y_l_ax, a, y))
            return false;
        if (a.is_one())
            return false;
        for (auto si : s.m_search) {
            if (!si.is_boolean())
                continue;
            if (si.is_resolved())
                continue;
            auto d = s.lit2cnstr(si.lit());
            if (!d->is_ule())
                continue;
            auto x_l_z = inequality::from_ule(d);
            if (is_g_v(x, x_l_z) && try_y_l_ax_and_x_l_z(x, core, y_l_ax, x_l_z, a, y))
                return true;
        }
        return false;
    }

    bool saturation::try_y_l_ax_and_x_l_z(pvar x, conflict& core, inequality const& y_l_ax, inequality const& x_l_z, pdd const& a, pdd const& y) {
        SASSERT(is_g_v(x, x_l_z));
        SASSERT(verify_Y_l_Ax(x, y_l_ax, a, y));
        pdd const& z = x_l_z.rhs();
        signed_constraint non_ovfl;
        if (!is_non_overflow(a, z, non_ovfl))
            return false;
        m_lemma.reset();
        m_lemma.insert_eval(~non_ovfl);
        return add_conflict(x, core, y_l_ax, x_l_z, ineq(x_l_z.is_strict() || y_l_ax.is_strict(), y, a * z));
    }

    /**
     * [x] a <= k & a*x + b = 0 & b = 0 => a = 0 or x = 0 or x >= 2^K/k
     * [x] x <= k & a*x + b = 0 & b = 0 => x = 0 or a = 0 or a >= 2^K/k
     * Better?
     * [x] a*x + b = 0 & b = 0 => a = 0 or x = 0 or Ω*(a, x)     
     * We need up to four versions of this for all sign combinations of a, x
     */
    bool saturation::try_mul_bounds(pvar x, conflict& core, inequality const& axb_l_y) {
        set_rule("[x] a*x + b = 0 & b = 0 => a = 0 or x = 0 or ovfl(a, x)");
        auto& m = s.var2pdd(x);
        pdd y = m.zero();
        pdd a = m.zero();
        pdd b = m.zero();
        pdd k = m.zero();
        pdd X = s.var(x);
        rational k_val;
        if (!is_AxB_eq_0(x, axb_l_y, a, b, y))
            return false;
        if (a.is_val())
            return false;        
        if (!is_forced_eq(b, 0))
            return false;

        signed_constraint x_eq_0, a_eq_0;
        if (!is_forced_diseq(X, 0, x_eq_0))
            return false;
        if (!is_forced_diseq(a, 0, a_eq_0))
            return false;

        auto prop1 = [&](signed_constraint c) {
            m_lemma.reset();
            m_lemma.insert_eval(~s.eq(b));
            m_lemma.insert_eval(~s.eq(y));
            m_lemma.insert_eval(x_eq_0);
            m_lemma.insert_eval(a_eq_0);
            return propagate(x, core, axb_l_y, c);
        };

        auto prop2 = [&](signed_constraint ante, signed_constraint c) {
            m_lemma.reset();
            m_lemma.insert_eval(~s.eq(b));
            m_lemma.insert_eval(~s.eq(y));
            m_lemma.insert_eval(x_eq_0);
            m_lemma.insert_eval(a_eq_0);
            m_lemma.insert_eval(~ante);
            return propagate(x, core, axb_l_y, c);
        };

        pdd minus_a = -a;
        pdd minus_X = -X;
        pdd Y = X;
        for (auto si : s.m_search) {
            if (!si.is_boolean())
                continue;
            if (si.is_resolved())
                continue;
            auto d = s.lit2cnstr(si.lit());
            if (!d->is_ule())
                continue;
            auto u_l_k = inequality::from_ule(d);
            // a <= k or x <= k
            k = u_l_k.rhs();
            if (!k.is_val())
                continue;
            k_val = k.val();
            if (u_l_k.is_strict())
                k_val -= 1;
            if (k_val <= 1)
                continue;
            if (u_l_k.lhs() == a || u_l_k.lhs() == minus_a) 
                Y = X;
            else if (u_l_k.lhs() == X || u_l_k.lhs() == minus_X) 
                Y = a;
            else
                continue;
            //
            // NSB review: should we handle cases where k_val >= 2^{K-1}, but exploit that x*y = 0 iff -x*y = 0?
            // 
            // IF_VERBOSE(0, verbose_stream() << "mult-bounds2 " << Y << " " << axb_l_y << " " << u_l_k<< " \n");
            rational bound = ceil(rational::power_of_two(m.power_of_2()) / k_val);
            if (prop2(d, s.uge(Y, bound)))
                return true;
            if (prop2(d, s.uge(-Y, bound)))
                return true;                     
        }

        // IF_VERBOSE(0, verbose_stream() << "mult-bounds1 " << a << " " << axb_l_y << " \n");
        // IF_VERBOSE(0, verbose_stream() << core << "\n"); 
        if (prop1(s.umul_ovfl(a, X)))
            return true;
        if (prop1(s.umul_ovfl(a, -X)))
            return true;
        if (prop1(s.umul_ovfl(-a, X)))
            return true;
        if (prop1(s.umul_ovfl(-a, -X)))
            return true;

        return false;
    }


    // bench 5
    // fairly ad-hoc rule derived from bench 5.
    // The clause could also be added whenever narrowing the literal 2^k*x = 2^k*y
    // It can be expected to be relatively common because these equalities come from
    // bit-masking.
    // 
    // A bigger hammer for detecting such propagations may be through LIA or a variant
    // 
    // a*x - a*y + b*z = 0 0 <= x < b/a, 0 <= y < b/a => z = 0
    // and then => x = y
    // 
    // the general lemma is that the linear term a*p = 0 is such that a*p does not overflow
    // and therefore p = 0
    // 
    // TBD: encode the general lemma instead of this special case.
    // 
    bool saturation::try_mul_eq_bound(pvar x, conflict& core, inequality const& axb_l_y) {
        set_rule("[x] 2^k*x = 2^k*y & x < 2^N-k => y = x or y >= 2^{N-k}");
        auto& m = s.var2pdd(x);
        unsigned N = m.power_of_2();
        pdd y = m.zero();
        pdd a = y, b = y, a2 = y;
        pdd X = s.var(x);
        if (!is_AxB_eq_0(x, axb_l_y, a, b, y))
            return false;
        if (!a.is_val())
            return false;
        if (!a.val().is_power_of_two())
            return false;
        unsigned k = a.val().trailing_zeros();
        if (k == 0)
            return false;
        b = -b;
        if (b.leading_coefficient() != a.val())
            return false;
        for (auto c : core) {
            if (!c->is_ule())
                continue;
            auto i = inequality::from_ule(c);
            if (!is_x_l_Y(x, i, a2))
                continue;
            if (!a2.is_val())
                continue;
            // x*2^k = b, x <= a2 < 2^{N-k}
            rational bound = rational::power_of_two(N - k);
            if (i.is_strict() && a2.val() >= bound)
                continue;
            if (!i.is_strict() && a2.val() > bound)
                continue;            
            pdd Y = b.div(b.leading_coefficient());
            rational Y_val;
            if (!s.try_eval(Y, Y_val) || Y_val >= bound)
                continue;
            signed_constraint le = s.ule(Y, bound - 1);
            m_lemma.reset();
            m_lemma.insert_eval(~le);
            m_lemma.insert_eval(~s.eq(y));
            m_lemma.insert(~c);
            if (propagate(x, core, axb_l_y, s.eq(X, Y)))
                return true;
        }

        return false;
    }

    /*
     * x*y = 1 & ~ovfl(x,y) => x = 1 
     * x*y = -1 & ~ovfl(-x,y) => -x = 1 
     */
    bool saturation::try_mul_eq_1(pvar x, conflict& core, inequality const& axb_l_y) {
        set_rule("[x] ax + b <= y & y = 0 & b = -1 & ~ovfl(a,x) => x = 1");
        auto& m = s.var2pdd(x);
        pdd y = m.zero();
        pdd a = m.zero();
        pdd b = m.zero();
        pdd X = s.var(x);
        signed_constraint non_ovfl;
        if (!is_AxB_eq_0(x, axb_l_y, a, b, y))
            return false;
        if (!is_forced_eq(b, -1))
            return false;
        if (!is_non_overflow(a, X, non_ovfl)) 
            return false;
        m_lemma.reset();
        m_lemma.insert_eval(~s.eq(b, rational(-1)));
        m_lemma.insert_eval(~s.eq(y));
        m_lemma.insert_eval(~non_ovfl);
        if (propagate(x, core, axb_l_y, s.eq(X, 1)))
            return true;
        if (propagate(x, core, axb_l_y, s.eq(a, 1)))
            return true;
        return false;
    }

    /**
     * odd(x*y) => odd(x) 
     * even(x) => even(x*y)
     *
     * parity(x) <= parity(x*y)
     * parity(x) = k & parity(x*y) = k + j => parity(y) = j
     * parity(x) = k & parity(y) = j => parity(x*y) = k + j
     *
     * odd(x) & even(y) => x + y != 0
     *
     * Special case rule: a*x + y = 0 => (odd(b) <=> odd(a) & odd(x))
     *
     * General rule:
     * 
     * a*x + y = 0 => min(K, parity(a) + parity(x)) = parity(y)
     * 
     * using inequalities:
     *
     * parity(x) <= i, parity(a) <= j => parity(b) <= i + j
     * parity(x) >= i, parity(a) >= j => parity(b) >= i + j
     * parity(x) <= i, parity(b) >= j => parity(a) >= j - i
     * parity(x) >= i, parity(b) <= j => parity(a) <= j - i 
     * symmetric rules for swapping x, a
     * 
     * min_parity(x) = number of trailing bits of x if x is a value
     * min_parity(x) = k if 2^{N-k}*x == 0 is forced for max k
     * min_parity(x1*x2) = min_parity(x1) + min_parity(x2)
     * min_parity(x) = 0, otherwise
     * 
     * max_parity(x) = number of trailing bits of x
     * max_parity(x) = k if 2^{N-k-1}*x != 0 for min k
     * max_parity(x1*x2) = max_parity(x1) + max_parity(x2)
     * max_parity(x) = N, otherwise
     * 
     */

    unsigned saturation::min_parity(pdd const& p) {
        rational val;
        auto& m = p.manager();
        unsigned N = m.power_of_2();
        if (s.try_eval(p, val))
            return val == 0 ? N : val.trailing_zeros();

#if 0
        // TBD: factor p
        auto coeff = p.leading_coefficient();
        unsigned offset = coeff.trailing_zeros();        
        verbose_stream() << "COEFF " << coeff << "\n";
#endif
#if 0
        unsigned j = 0;
        while (j < N && is_forced_true(s.parity(p, j + 1)))
            ++j;
        return j;
#else
        for (unsigned j = N; j > 0; --j)
            if (is_forced_true(s.parity(p, j)))
                return j;
        return 0;
#endif
    }

    unsigned saturation::max_parity(pdd const& p) {
        auto& m = p.manager();
        unsigned N = m.power_of_2();
        rational val;
        if (s.try_eval(p, val))
            return val == 0 ? N : val.trailing_zeros();

        // TBD: factor p

        for (unsigned j = 0; j < N; ++j) 
            if (is_forced_true(s.parity_at_most(p, j)))
                return j;
        return N;
    }

    bool saturation::try_parity(pvar x, conflict& core, inequality const& axb_l_y) {
        set_rule("[x] a*x + b = 0 => (odd(a) & odd(x) <=> odd(b))");
        auto& m = s.var2pdd(x);
        unsigned N = m.power_of_2();
        pdd y = m.zero();
        pdd a = y, b = y;
        pdd X = s.var(x);
        if (!is_AxB_eq_0(x, axb_l_y, a, b, y))
            return false;
        if (a.is_max() && b.is_var())  // x == y, we propagate values in each direction and don't need a lemma
            return false;
        if (a.is_one() && (-b).is_var())  // y == x
            return false;
        if (a.is_one())
            return false;
        if (a.is_val() && b.is_zero())
            return false;

        auto propagate1 = [&](signed_constraint premise, signed_constraint conseq) {
            if (is_forced_false(premise))
                return false;
            IF_VERBOSE(1, verbose_stream() << "propagate " << axb_l_y << " " << premise << " => " << conseq << "\n");
            m_lemma.reset();
            m_lemma.insert_eval(~s.eq(y));
            m_lemma.insert_eval(~premise);
            return propagate(x, core, axb_l_y, conseq);
        };

        auto propagate2 = [&](signed_constraint premise1, signed_constraint premise2, signed_constraint conseq) {
            if (is_forced_false(premise1))
                return false;
            if (is_forced_false(premise2))
                return false;
            IF_VERBOSE(1, verbose_stream() << "propagate " << axb_l_y << " " << premise1 << " " << premise2 << " => " << conseq << "\n");
            m_lemma.reset();
            m_lemma.insert_eval(~s.eq(y));
            m_lemma.insert_eval(~premise1);
            m_lemma.insert_eval(~premise2);
            return propagate(x, core, axb_l_y, conseq);
        };

        unsigned min_x = min_parity(X), max_x = max_parity(X);
        unsigned min_b = min_parity(b), max_b = max_parity(b);
        unsigned min_a = min_parity(a), max_a = max_parity(a);
        SASSERT(min_x <= max_x && max_x <= N);
        SASSERT(min_a <= max_a && max_a <= N);
        SASSERT(min_b <= max_b && max_b <= N);

        IF_VERBOSE(2, 
                   verbose_stream() << "try parity v" << x << " " << axb_l_y << "\n";
                   verbose_stream() << X << " " << min_x << " " << max_x << "\n";
                   verbose_stream() << a << " " << min_a << " " << max_a << "\n";
                   verbose_stream() << b << " " << min_b << " " << max_b << "\n");                    

        if (min_x >= N || min_a >= N)
            return false;

        auto at_most = [&](pdd const& p, unsigned k) {
            VERIFY(k < N);
            return s.parity_at_most(p, k);
        };

        auto at_least = [&](pdd const& p, unsigned k) {
            VERIFY(k != 0);
            return s.parity(p, k);
        };

 
        if (!b.is_val() && max_b > max_a + max_x && propagate2(at_most(a, max_a), at_most(X, max_x), at_most(b, max_x + max_a)))
            return true;
        if (!b.is_val() && min_x > min_b && propagate1(at_least(X, min_x), at_least(b, min_x)))
            return true;
        if (!b.is_val() && min_a > min_b && propagate1(at_least(a, min_a), at_least(b, min_a)))
            return true;
        if (!b.is_val() && min_x > 0 && min_a > 0 && min_x + min_a > min_b && propagate2(at_least(a, min_a), at_least(X, min_x), at_least(b, min_a + min_x)))
            return true;
        if (!a.is_val() && max_x <= min_b && min_a < min_b - max_x && propagate2(at_most(X, max_x), at_least(b, min_b), at_least(a, min_b - max_x)))
            return true;
        if (max_a <= min_b && min_x < min_b - max_a && propagate2(at_most(a, max_a), at_least(b, min_b), at_least(X, min_b - max_a)))
            return true;
        if (max_b < N && !a.is_val() && min_x > 0 && min_x <= max_b && max_a > max_b - min_x && propagate2(at_least(X, min_x), at_most(b, max_b), at_most(a, max_b - min_x)))
            return true;
        if (max_b < N && min_a > 0 && min_a <= max_b && max_x > max_b - min_a && propagate2(at_least(a, min_a), at_most(b, max_b), at_most(X, max_b - min_a)))
            return true;

        return false;        
    }

    /**
     *  2^{K-1}*x*y != 0 => odd(x) & odd(y)
     *  2^k*x != 0 => parity(x) < K - k
     *  2^k*x*y != 0 => parity(x) + parity(y) < K - k
     */
    bool saturation::try_parity_diseq(pvar x, conflict& core, inequality const& axb_l_y) {
        set_rule("[x] 2^k*x*y != 0 => parity(x) + parity(y) < K - k");
        auto& m = s.var2pdd(x);
        unsigned N = m.power_of_2();
        pdd y = m.zero();
        pdd a = y, b = y;
        pdd X = s.var(x);
        if (!is_AxB_diseq_0(x, axb_l_y, a, b, y))
            return false;
        if (!is_forced_eq(b, 0))
            return false;
        auto coeff = a.leading_coefficient();
        if (coeff.is_odd())
            return false;
        SASSERT(coeff != 0);
        unsigned k = coeff.trailing_zeros();
        m_lemma.reset();
        m_lemma.insert_eval(~s.eq(y));
        m_lemma.insert_eval(~s.eq(b));        
        if (propagate(x, core, axb_l_y, ~s.parity(X, N - k)))
            return true;

        return false;
    }

    /**
     * a*x = 0 => a = 0 or even(x)
     * a*x = 0 => a = 0 or x = 0 or even(a)
     */
    bool saturation::try_mul_odd(pvar x, conflict& core, inequality const& axb_l_y) {
        set_rule("[x] ax = 0 => a = 0 or even(x)");
        auto& m = s.var2pdd(x);
        pdd y = m.zero();
        pdd a = m.zero();
        pdd b = m.zero();
        pdd X = s.var(x);
        signed_constraint a_eq_0, x_eq_0;
        if (!is_AxB_eq_0(x, axb_l_y, a, b, y))
            return false;
        if (!is_forced_eq(b, 0))
            return false;
        if (!is_forced_diseq(a, 0, a_eq_0))
            return false;
        m_lemma.reset();
        m_lemma.insert_eval(s.eq(y));
        m_lemma.insert_eval(~s.eq(b));
        m_lemma.insert_eval(a_eq_0);
        if (propagate(x, core, axb_l_y, s.even(X)))
            return true;
        if (!is_forced_diseq(X, 0, x_eq_0))
            return false;
        m_lemma.insert_eval(x_eq_0);
        if (propagate(x, core, axb_l_y, s.even(a)))
            return true;
        return false;
    }

    /**
     * TODO If both inequalities are strict, then the implied inequality has a gap of 2
     * a < b, b < c => a + 1 < c & a + 1 != 0
     */
    bool saturation::try_transitivity(pvar x, conflict& core, inequality const& a_l_b) {
        set_rule("[x] q < x & x <= p => q < p");
        auto& m = s.var2pdd(x);
        pdd p = m.zero();
        pdd a = p, b = p, q = p;
        // x <= p
        if (!is_Ax_l_Y(x, a_l_b, a, p))
            return false;
        if (!is_forced_eq(a, 1))
            return false;
        for (auto c : core) {
            if (!c->is_ule())
                continue;
            auto i = inequality::from_ule(c);
            if (c == a_l_b.as_signed_constraint())
                continue;
            if (!is_Y_l_Ax(x, i, b, q))
                continue;
            if (!is_forced_eq(b, 1))
                continue;
            m_lemma.reset();
            m_lemma.insert_eval(~s.eq(a, 1));
            m_lemma.insert_eval(~s.eq(b, 1));
            m_lemma.insert(~c);
            auto ineq = i.is_strict() || a_l_b.is_strict() ? (p.is_val() ? s.ule(q, p - 1) : s.ult(q, p)) : s.ule(q, p);
            if (propagate(x, core, a_l_b, ineq))
                return true;
        }

        return false;
    }

    /**
     * p <= q, q <= p => p - q = 0
     */
    bool saturation::try_infer_equality(pvar x, conflict& core, inequality const& a_l_b) {
        set_rule("[x] p <= q, q <= p => p - q = 0");
        if (a_l_b.is_strict())
            return false;
        if (a_l_b.lhs().degree(x) == 0 && a_l_b.rhs().degree(x) == 0)
            return false;
        for (auto c : core) {
            if (!c->is_ule())
                continue;
            auto i = inequality::from_ule(c);
            if (i.lhs() == a_l_b.rhs() && i.rhs() == a_l_b.lhs() && !i.is_strict()) {
                m_lemma.reset();
                m_lemma.insert(~c);
                if (propagate(x, core, a_l_b, s.eq(i.lhs() - i.rhs()))) {
                    verbose_stream() << "infer equality " << s.eq(i.lhs() - i.rhs()) << "\n";
                    return true;
                }
            }
        }
        return false;
    }



    bool saturation::try_factor_equality(pvar x, conflict& core, inequality const& a_l_b) {
        set_rule("[x] ax + b = 0 & C[x] => C[-inv(a)*b]");
        auto& m = s.var2pdd(x);       
        pdd y  = m.zero();
        pdd a = y, b = y, a1 = y, b1 = y;        
        if (!is_AxB_eq_0(x, a_l_b, a, b, y))
            return false;
        bool is_invertible = a.is_val() && a.val().is_odd();
        if (is_invertible) {
            rational a_inv;
            VERIFY(a.val().mult_inverse(m.power_of_2(), a_inv));
            b = -b*a_inv;
        }
        bool change = false;
        bool prop = false;
        auto replace = [&](pdd p) {
            unsigned p_degree = p.degree(x);
            if (p_degree == 0)
                return p;
            if (is_invertible) {
                change = true;
                return p.subst_pdd(x, b);
            }
            if (p_degree == 1) {
                p.factor(x, 1, a1, b1);
                if (a1 == a) {
                    change = true;
                    return b1 - b;
                }
                if (a1 == -a) {
                    change = true;
                    return b1 + b;
                }
            }
            return p;            
        };
        
        for (auto c : core) {
            change = false;
            if (c == a_l_b.as_signed_constraint())
                continue;
            if (c->is_ule()) {
                auto const& ule = c->to_ule();
                auto p = replace(ule.lhs());
                auto q = replace(ule.rhs());
                if (!change)
                    continue;
                m_lemma.reset();
                m_lemma.insert(~c);
                m_lemma.insert_eval(~s.eq(y));
                if (propagate(x, core, a_l_b, c.is_positive() ? s.ule(p, q) : ~s.ule(p, q)))
                    prop = true;
            }
            else if (c->is_umul_ovfl()) {
                auto const& ovf = c->to_umul_ovfl();
                auto p = replace(ovf.p());
                auto q = replace(ovf.q());
                if (!change)
                    continue;
                m_lemma.reset();
                m_lemma.insert(~c);
                m_lemma.insert_eval(~s.eq(y));
                if (propagate(x, core, a_l_b, c.is_positive() ? s.umul_ovfl(p, q) : ~s.umul_ovfl(p, q)))
                    prop = true;
            }
        }
        return prop;
    }


    /**
     *  x >= x + y & x <= n => y = 0 or y >= N - n
     *  x >  x + y & x <= n => y >= N - n
     * -x <= -x - y & x <= n => y = 0 or y >= N - n
     * -x < -x - y & x <= n => y >= N - n
     */
    bool saturation::try_add_overflow_bound(pvar x, conflict& core, inequality const& axb_l_y) {
        set_rule("[x] x >= x + y & x <= n => y = 0 or y >= 2^N - n");
        signed_constraint y_eq_0;
        vector<signed_constraint> x_ge_bound;
        auto& m = s.var2pdd(x);
        pdd y = m.zero();
        if (!is_add_overflow(x, axb_l_y, y))
            return false;
        if (!axb_l_y.is_strict() && !is_forced_diseq(y, 0, y_eq_0))
            return false;
        rational bound;
        if (!has_upper_bound(x, core, bound, x_ge_bound))
            return false;
        SASSERT(bound != 0);
        m_lemma.reset();
        if (!axb_l_y.is_strict())
            m_lemma.insert_eval(y_eq_0);        
        for (auto c : x_ge_bound)
            m_lemma.insert_eval(~c);
        return propagate(x, core, axb_l_y, s.uge(y, m.two_to_N() - bound));
    }

    /**
     * Match one of the patterns:
     * x >= x + y
     * x > x + y
     * -x <= -x - y
     * -x < -x - y
     */
    bool saturation::is_add_overflow(pvar x, inequality const& i, pdd& y) {
        auto& m = s.var2pdd(x);        
        pdd X = s.var(x);
        pdd a = X;
        if (i.lhs().degree(x) != 1 || i.rhs().degree(x) != 1)
            return false;
        if (i.rhs() == X) {
            i.lhs().factor(x, 1, a, y);
            if (a.is_one())
                return true;
        }
        if (i.lhs() == -X) {
            i.rhs().factor(x, 1, a, y);
            if ((-a).is_one()) {
                y = -y;
                return true;
            }
        }
        return false;
    }

    bool saturation::has_upper_bound(pvar x, conflict& core, rational& bound, vector<signed_constraint>& x_le_bound) {
        return s.m_viable.has_upper_bound(x, bound, x_le_bound);
    }

    bool saturation::has_lower_bound(pvar x, conflict& core, rational& bound, vector<signed_constraint>& x_ge_bound) {
        return s.m_viable.has_lower_bound(x, bound, x_ge_bound);
    }

    /*
     * Bounds propagation for base case ax <= y
     * where
     *  & y <= u_y
     *  & 0 < x <= u_x
     *
     * Special case for interval including -1
     * Compute max n, such that a \not\in [-n,0[ is implied, then 
     *
     * => a < -n
     * Claim n = floor(- u_y / u_x), 
     * - provided n != 0
     *
     * Justification: for a1 in [1,n[ :
     *        0 < a1*x <= floor (- u_y / u_x) * u_x
     *                 <= - u_y
     * and therefore for a1 in [-n-1:0[ :
     *        u_y < a1*x < 0
     *
     * 
     * Bounds case for additive case ax - b <= y
     * where
     *  & y <= u_y
     *  & b <= u_b
     *  & u_y + u_b does not overflow (implies y + b >= y)
     *  => ax - b + b <= y + b
     *  => ax <= y + b
     *  => ax <= u_y + u_b
     * 
     * Base case for additive case ax + b <= y
     * where
     *  & y <= u_y
     *  & b >= l_b
     *  & ax + b >= b 
     * 
     *  => ax + b - b <= y - b
     *  => ax <= y - b
     *  => ax <= u_y - l_b
     * 
     * TODO - deal with side condition ax + b >= b?
     * It requires that ax + b does not overflow
     * If the literal is already assigned, we are fine, otherwise?
     * 
     *
     * Example (bench25) 
     * -1*v85*v33 + v81 <= 2^128-2
     * v33 <= 2^128-1
     * v81 := -1
     * v85 := 12
     *
     * Example (bench25)
     * -1489: v25 > -1*v85*v25 + v81
     * 2397: v85 + 1 <= 328022915686448145675838484443875093068753497636375535522542730900603766685
     * -1195: v85 + 1 > 2^128+1
     * v25 := 353
     * v81 := -1
     *
     * -1*v85*v25 + v81 < v25    
     * a -1*v25 := -315  b v81 := -1   y v25 := 315
     * & v25 <= 315
     * & -v81 <= 1 
     * 
     * The example illustrates that fixing y_val produces a weaker bound.
     * The result should be a forbidden interval around v25 based on bounds for
     * v85 and v81.
     *
     * The example also illustrates that presumably just a combination of forbidden intervals for v85 used in the conflict
     * are sufficient for narrowing the bounds on v81. Querying for upper/lower bounds of v85 doesn't produce the strongest
     * assumption. 2397 and -1195 come from unit intervals with fixed lo/hi.
     * 
     * On the other hand, the bound v25 > -1*v85*v25 + v81 was obtained by evaluating v25 and v81
     * and the quantifier elimination based on viable::resolve_lemma didn't produce the most general lemma. 
     * Instead it relied on the evaluation at 353 and -1, respectively.
     * 
     */
    
    bool saturation::try_add_mul_bound(pvar x, conflict& core, inequality const& a_l_b) {
        set_rule("[x] ax + b <= y, ... => a >= u_a");
        auto& m = s.var2pdd(x);        
        pdd const X = s.var(x);
        pdd a = s.var(x);
        pdd b = a, c = a, y = a;
        rational a_val, b_val, c_val, y_val, x_bound;
        vector<signed_constraint> x_le_bound, x_ge_bound;
        signed_constraint b_bound;
        if (is_AxB_l_Y(x, a_l_b, a, b, y) && !a.is_val() && s.try_eval(y, y_val) && s.try_eval(b, b_val) && s.try_eval(a, a_val) && !y_val.is_zero()) {
            IF_VERBOSE(2, verbose_stream() << "v" << x << ": " << a_l_b << "   a " << a << " := " << dd::val_pp(m, a_val, false) << "  b " << b << " := " << dd::val_pp(m, b_val, false) << "   y " << y << " := " << dd::val_pp(m, y_val, false) << "\n");
            SASSERT(!a.is_zero());

            // define c := -b
            c = -b;
            VERIFY(s.try_eval(c, c_val));

            if (has_upper_bound(x, core, x_bound, x_le_bound) && !x_le_bound.contains(a_l_b.as_signed_constraint())) {
                // ax - c <= y
                // ==>  ax <= y + c                              if int(y) + int(c) <= 2^N, y <= int(y), c <= int(c)
                // ==>  a not in [-floor(-int(y+c) / int(x), 0[
                // ==>  -a >= floor(-int(y+c) / int(x)
                if (c_val + y_val <= m.max_value()) {
                    auto bound = floor((m.two_to_N() - y_val - c_val) / x_bound);
                    m_lemma.reset();
                    for (auto c : x_le_bound)
                        m_lemma.insert_eval(~c);               // x <= x_bound
                    m_lemma.insert_eval(~s.ule(c, c_val));      // c <= c_val
                    m_lemma.insert_eval(~s.ule(y, y_val));      // y <= y_val
                    auto conclusion = s.uge(-a, bound);         // ==>  -a >= bound
                    IF_VERBOSE(2, 
                               verbose_stream() << core << "\n";
                               verbose_stream() << "& " << X << " <= " << dd::val_pp(m, x_bound, false) << " := " << x_le_bound << "\n";
                               verbose_stream() << "& " << s.ule(c, c_val) << "\n";
                               verbose_stream() << "& " << s.ule(y, y_val) << "\n";
                               verbose_stream() << "==> " << -a << " >= " << dd::val_pp(m, bound, false) << "\n");
                    if (propagate(x, core, a_l_b, conclusion)) 
                        return true;
                }
                // verbose_stream() << "TODO bound 1 " << a_l_b << " " << x_ge_bound << " " << b << " " << b_val << " " << y << "\n";
            }
#if 0
            if (has_lower_bound(x, core, x_bound, x_le_bound) && !x_le_bound.contains(a_l_b.as_signed_constraint())) {
                
                // verbose_stream() << "TODO bound 2 " << a_l_b << " " << x_le_bound << "\n";
            }
#endif
        }
        if (is_Y_l_AxB(x, a_l_b, y, a, b) && y.is_val() && s.try_eval(b, b_val)) {
            // verbose_stream() << "TODO bound 3 " << a_l_b << "\n";
        }
        return false;
    }

    
    /*
     * TODO
     *
     * Maybe also
     * x*y = k => \/_{j is such that there is j', j*j' = k} x = j
     * x*y = k & ~ovfl(x,y) & x = j => y = k/j where j is a divisor of k
     */


    /**
     * [x] p(x) <= q(x) where value(p) > value(q)
     *     ==> q <= value(q) => p <= value(q)
     *
     * for strict?
     *     p(x) < q(x) where value(p) >= value(q)
     *     ==> value(p) <= p => value(p) < q
     */
    bool saturation::try_tangent(pvar v, conflict& core, inequality const& c) {
        set_rule("[x] p(x) <= q(x) where value(p) > value(q)");
        // if (c.is_strict())
        //     return false;
        if (!c.as_signed_constraint()->contains_var(v))
            return false;
        if (c.lhs().is_val() || c.rhs().is_val())
            return false;

        auto& m = s.var2pdd(v);
        pdd q_l(m), e_l(m), q_r(m), e_r(m);
        bool is_linear = true;
        is_linear &= c.lhs().degree(v) <= 1;
        is_linear &= c.rhs().degree(v) <= 1;
        if (c.lhs().degree(v) == 1) {
            c.lhs().factor(v, 1, q_l, e_l);
            is_linear &= q_l.is_val();
        }
        if (c.rhs().degree(v) == 1) {
            c.rhs().factor(v, 1, q_r, e_r);
            is_linear &= q_r.is_val();
        }
        if (is_linear)
            return false;

        if (!c.as_signed_constraint().is_currently_false(s))
            return false;
        rational l_val, r_val;
        if (!s.try_eval(c.lhs(), l_val))
            return false;
        if (!s.try_eval(c.rhs(), r_val))
            return false;
        SASSERT(c.is_strict() || l_val > r_val);
        SASSERT(!c.is_strict() || l_val >= r_val);
        m_lemma.reset();
        if (c.is_strict()) {
            auto d = s.ule(l_val, c.lhs());
            if (d.bvalue(s) == l_false) // it is a different value conflict that contains v
                return false;
            m_lemma.insert_eval(~d);
            auto conseq = s.ult(r_val, c.rhs());
            return add_conflict(v, core, c, conseq);
        }
        else {
            auto d = s.ule(c.rhs(), r_val);
            if (d.bvalue(s) == l_false) // it is a different value conflict that contains v
                return false;
            m_lemma.insert_eval(~d);
            auto conseq = s.ule(c.lhs(), r_val);
            return add_conflict(v, core, c, conseq);
        }
    }

}
