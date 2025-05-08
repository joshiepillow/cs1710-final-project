#lang forge/temporal

option max_tracelength 12
option min_tracelength 12

sig Person {}

sig List {
    person : one Person,
    next : lone List
}

abstract sig Group {
    priorities : set Person -> List
}

sig Roommates {
    others: set Person
}

sig Match {
    n_mates: set Person -> Roommates
}

one sig Female extends Group{}
one sig Male extends Group {}

pred init {
    Person in Female.priorities.List + Male.priorities.List // Every person is in Female or in Male
    no Female.priorities.List & Male.priorities.List // No one is in Female in Male
    #{Female.priorities} = #{Male.priorities} // Same size
    all p: Person {
        // Only one ranking per person
        lone (p -> List) & Female.priorities
        lone (p -> List) & Male.priorities

        // Every member ranks all other members
        p in Female.priorities.List implies (Female.priorities[p]).*next.person = Male.priorities.List
        p in Male.priorities.List implies (Male.priorities[p]).*next.person = Female.priorities.List
    }
    all l: List {
        l.person not in l.^next.person // No ranking includes the same person twice
        l in Person.(Group.priorities).*next // No dangling irrelevant lists
    }
}

run { init } for exactly 6 Person, exactly 6 List

pred valid_match[m: Match] {
    // No one is matched to themselves
    no p: Person | p in (m.n_mates[p]).others

    // Matching is symmetric
    all p1, p2: Person |
        p2 in (m.n_mates[p1]).others implies p1 in (m.n_mates[p2]).others

    // Matching is transitive (include disj for self-match case)
    all disj p1, p2, p3: Person |
        (p2 in (m.n_mates[p1]).others and p3 in (m.n_mates[p1]).others) implies p3 in (m.n_mates[p2]).others 

    // Everyone is matched to exactly one set of roommates
    all p: Person | one m.n_mates[p]
    all disj p1, p2: Person | m.n_mates[p1] != m.n_mates[p2]

    // Everyone is matched to exactly two people
    all p: Person | let n = 2 | (#{p1: Person | p1 in (m.n_mates[p]).others} = n)

    // All roommates must be from the same group
    all p: Person | 
        (p in Female.priorities.List implies (m.n_mates[p]).others in Female.priorities.List) and
        (p in Male.priorities.List implies (m.n_mates[p]).others in Male.priorities.List)

}

run {
    init
    some m: Match | valid_match[m]
} for exactly 9 Person, exactly 9 List, exactly 9 Roommates, exactly 1 Match


pred stable_match[m: Match] {
  valid_match[m]

  no a, b: Person |
    let aList = Female.priorities[a] |
    let bList = Male.priorities[b] |
    let aMatch = (m.n_mates[a]).others |
    let bMatch = (m.n_mates[b]).others |
    let aNext = ^next[aList] |
    let bNext = ^next[bList] |
    b not in aMatch and
    a != b and 
    {some l1, l2, l3, l4: List | 
    l1 in aList.*next and l2 in aList.*next and
    l1.person = b and l2.person in aMatch and
    l2 in ^next[l1] and  // a prefers b over aMatch
    l3 in bList.*next and l4 in bList.*next and
    l3.person = a and l4.person in bMatch and
    l4 in ^next[l3]  // b prefers a over bMatch
    }
}

run {
    init
    some m: Match | stable_match[m]
} for exactly 6 Person, exactly 6 List, exactly 6 Roommates, exactly 1 Match
