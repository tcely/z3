/*++
Copyright (c) 2023 Microsoft Corporation

Module Name:

    expr_polarities.cpp

Abstract:

    Extract polarities of expressions.

Author:

    Nikolaj Bjorner (nbjorner) 2023-06-01

--*/
#pragma once

#include "ast/expr_polarities.h"

void expr_polarities::push() {
    m_fresh_lim.push_back(m_fresh.size());
    m_trail_lim.push_back(m_trail.size());
}
    
void expr_polarities::pop(unsigned n) {
    unsigned sz = m_fresh_lim[m_fresh_lim.size() - n];
    for (unsigned i = m_fresh_lim.size(); --i > sz; ) {
        auto const & [e, p] = m_fresh[i];
        if (p)
            m_pos.mark(e, false);
        else
            m_neg.mark(e, false);        
    }
    m_fresh.shrink(sz);
    m_fresh_lim.shrink(m_fresh_lim.size() - n);
    sz = m_trail_lim[m_trail_lim.size() - n];
    m_trail.shrink(sz);
    m_trail_lim.shrink(m_trail_lim.size() - n);
}

    
void expr_polarities::add(expr* e) {
    if (m_pos.is_marked(e))
        return;
    m_trail.push_back(e);
    buffer<std::pair<bool, expr*>> frames;
    frames.push_back({true, e});
    while (!frames.empty()) {
        auto [p, e] = frames.back();
        frames.pop_back();
        if (p) {
            if (m_pos.is_marked(e))
                continue;
            m_pos.mark(e, true);
        }
        else {
            if (m_neg.is_marked(e))
                continue;
            m_neg.mark(e, true);
        }
        m_fresh.push_back({e, p});
        if (m.is_and(e) || m.is_or(e)) {
            for (expr* arg : *to_app(e))
                frames.push_back({p, arg});
        }
        else if (m.is_not(e, e)) {
            frames.push_back({!p, e});
        }
        else if (m.is_implies(e)) {
            frames.push_back({!p, to_app(e)->get_arg(0)});
            frames.push_back({p, to_app(e)->get_arg(1)});
        }
        else if (is_app(e)) {
            for (expr* arg : *to_app(e)) {
                frames.push_back({true, arg});
                frames.push_back({false, arg});
            }
        }
        else if (is_quantifier(e)) 
            frames.push_back({p, to_quantifier(e)->get_expr()});        
    }
}
    


