#lang forge/temporal

open "two_person.frg"

pred match_to_different_group {
    all p: Person | { 
        some p1: Person, m: Match | { 
            p in GroupA.priorities.List <=> p1 in GroupB.priorities.List
            m.pair[p] = p1
        }
    }
}

pred all_valid_matches {
    all m: Match | { valid_match[m] }
}

test suite for valid_match {

    // there exists a match that satisfies the valid_match predicate
    valid_match_exists: assert { 
        init 
        some m: Match | valid_match[m] 
    } is sat 

    // for all valid matches, every person is partnered with exactly one other person 
    single_partner: assert {
        all p: Person | { 
            some p1: Person, m: Match | { 
                one m.pair[p]
                p != p1 and m.pair[p] = p1 and m.pair[p1] = p
            }
        }
    } is necessary for all_valid_matches for exactly 8 Person, exactly 8 List, exactly 4 Match

    // for all valid matches, every person matched with someone from a different group (given init constraints)
    different_group: assert {
        init
        all_valid_matches
    } is sufficient for match_to_different_group for exactly 8 Person, exactly 8 List, exactly 4 Match
}

pred both_unhappy {
    some a, b: Person, m: Match | {
        let aList = GroupA.priorities[a] + GroupB.priorities[a] | 
        let bList = GroupA.priorities[b] + GroupB.priorities[b] | 
        let aNext = ^next[aList] | 
        let bNext = ^next[bList] | 
        m.pair[a] != b and
        a != b and 
        {some l1, l2, l3, l4: List | 
            l1 in aList.*next and l2 in aList.*next and
            l1.person = b and l2.person = m.pair[a] and
            l2 in ^next[l1] and 
            l3 in bList.*next and l4 in bList.*next and
            l3.person = a and l4.person = m.pair[b] and
            l4 in ^next[l3] 
        }
    }
}

pred all_stable_matches {
    all m: Match | { stable_match[m] }
}

test suite for stable_match {
    
    // there exists a match that satisfies the stable_match predicate
    stable_match_exists: assert { 
        init 
        some m: Match | stable_match[m] 
    } is sat

    // the match that pairs everyone with their first choice is stable
    best_scenario: assert {
        init
        some m: Match | {
            all p: Person |  { 
                p in GroupA => ((GroupA.priorities[p]).person = m.pair[p]) 
                p in GroupB => ((GroupB.priorities[p]).person = m.pair[p])
            } => stable_match[m] 
        }
    } is sat for exactly 4 Person, exactly 4 List, exactly 1 Match

    // for all stable matches, there will be no case where two people want each other more than their current partner
    fair_allocation: assert {
        not both_unhappy
    } is necessary for all_stable_matches for exactly 4 Person, exactly 4 List, exactly 2 Match
}
   
