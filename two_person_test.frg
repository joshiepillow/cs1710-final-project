#lang forge/temporal

open "two_person.frg"

test suite for init {
    // Symmetric difference of Mentors and Mentees is the set of all Persons
    assert { 
        Person = Mentor.priorities.List + Mentee.priorities.List - Mentor.priorities.List & Mentee.priorities.List 
    } is necessary for init

    // Equal number of Mentors and Mentees
    assert {
        #{Mentor.priorities.List} = #{Mentee.priorities.List}
    } is necessary for init

    // Every Mentor ranks every Mentee once
    assert {
        all m1: Mentor.priorities.List, m2: Mentee.priorities.List | {
            one l: List | l in (Mentor.priorities[m1]).*next and l.person = m2
        }
    } is necessary for init
    // and vice versa.
    assert {
        all m1: Mentee.priorities.List, m2: Mentor.priorities.List | {
            one l: List | l in (Mentee.priorities[m1]).*next and l.person = m2
        }
    } is necessary for init

    // Preference list length equals number of pairs
    assert {
        all p: Person | #{(Group.priorities[p]).*next} = #{Mentor.priorities.List}
    } is necessary for init

    // No one ranks their own group
    assert {
        all m1: Mentor.priorities.List, m2: Mentor.priorities.List | {
            no l: List | l in (Mentor.priorities[m1]).*next and l.person = m2
        }
    } is necessary for init
    assert {
        all m1: Mentee.priorities.List, m2: Mentee.priorities.List | {
            no l: List | l in (Mentee.priorities[m1]).*next and l.person = m2
        }
    } is necessary for init
}

pred match_to_different_group {
    all p: Person | { 
        some p1: Person, m: Match | { 
            p in Mentor.priorities.List <=> p1 in Mentee.priorities.List
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
        let aList = Mentor.priorities[a] + Mentee.priorities[a] | 
        let bList = Mentor.priorities[b] + Mentee.priorities[b] | 
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
                p in Mentor => ((Mentor.priorities[p]).person = m.pair[p]) 
                p in Mentee => ((Mentee.priorities[p]).person = m.pair[p])
            } => stable_match[m] 
        }
    } is sat for exactly 4 Person, exactly 4 List, exactly 1 Match

    // for all stable matches, there will be no case where two people want each other more than their current partner
    fair_allocation: assert {
        not both_unhappy
    } is necessary for all_stable_matches for exactly 4 Person, exactly 4 List, exactly 2 Match
}
   
test suite for metrics {
-- 1. Egalitarian truly minimal total cost
    assert {
        init 
        all m1, m2: Match |
            isEgalitarian[m1] and valid_match[m1] and valid_match[m2] and
            totalCost[m1] >= totalCost[m2]
    } is unsat

    assert {
        init
        all m1, m2: Match |
            isGroupEqual[m1] and valid_match[m1] and valid_match[m2] and
            abs[groupCost[Mentor, m1] - groupCost[Mentee, m1]] <=
            abs[groupCost[Mentor, m2] - groupCost[Mentee, m2]]
    } is sat
}