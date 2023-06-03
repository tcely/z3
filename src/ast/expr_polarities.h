/*++
Copyright (c) 2023 Microsoft Corporation

Module Name:

    expr_polarities.h

Abstract:

    Extract polarities of expressions.

Author:

    Nikolaj Bjorner (nbjorner) 2023-06-01

--*/
#pragma once

#include "ast/ast.h"

class expr_polarities {
    ast_manager &    m;
    expr_ref_vector  m_trail;
    expr_mark        m_pos, m_neg;
    vector<std::pair<expr*, bool>> m_fresh;
    unsigned_vector m_fresh_lim, m_trail_lim;
public:
    expr_polarities(ast_manager & m) : m(m), m_trail(m) {}

    void push();
    
    void pop(unsigned n);

    // add expressions to annotate with polarities    
    void add(expr* e);
    
    void add(expr_ref_vector const& es) {
        for (expr* e : es)
            add(e);
    }

    bool has_negative(expr* e) const {
        return m_neg.is_marked(e);
    }
    
    bool has_positive(expr* e) const {
        return m_pos.is_marked(e);
    }
    
};


