#lang forge/temporal
option run_sterling "tp_visualizer.js"

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

sig Match {
    pair: set Person -> Person
}

one sig Interval {
    var intervals: set Person -> Person
}

one sig GroupA extends Group {}
one sig GroupB extends Group {}

pred init {
    Person in GroupA.priorities.List + GroupB.priorities.List // Every person is in either GroupA or GroupB
    no GroupA.priorities.List & GroupB.priorities.List // No one is in GroupA in GroupB
    #{GroupA.priorities} = #{GroupB.priorities} // Same size
    all p: Person {
        // Only one ranking per person
        lone (p -> List) & GroupA.priorities
        lone (p -> List) & GroupB.priorities

        // Every member of each group ranks all other members from the other group
        p in GroupA.priorities.List implies (GroupA.priorities[p]).*next.person = GroupB.priorities.List
        p in GroupB.priorities.List implies (GroupB.priorities[p]).*next.person = GroupA.priorities.List
    }
    all l: List {
        l.person not in l.^next.person // No ranking includes the same person twice
        l in Person.(Group.priorities).*next // No dangling irrelevant lists
    }
    // Initially all members of GroupA are considered by all members of GroupB and vice versa
    Interval.intervals = GroupA.priorities.List -> GroupB.priorities.List + GroupB.priorities.List -> GroupA.priorities.List
}

run { init } for exactly 4 Person, exactly 8 List

pred valid_match[m: Match] {
    // No one is matched to themselves
    no p: Person | m.pair[p] = p

    // Matching is symmetric
    all p1, p2: Person |
        m.pair[p1] = p2 implies m.pair[p2] = p1

    // Everyone is matched to exactly one person
    all p: Person | one m.pair[p]

    // No one is matched to someone in the same group
    all p1: Person | 
        let p2 = m.pair[p1] |
            (p1 in GroupA.priorities.List and p2 in GroupB.priorities.List) or
            (p1 in GroupB.priorities.List and p2 in GroupA.priorities.List)

     all l: List | some l.person
}

run {
    init
    some m: Match | valid_match[m]
} for exactly 4 Person, exactly 8 List, exactly 1 Match


pred stable_match[m: Match] {
  valid_match[m]

  no a, b: Person |
    let aList = GroupA.priorities[a] + GroupB.priorities[a] |
    let bList = GroupA.priorities[b] + GroupB.priorities[b] |
    let aMatch = m.pair[a] |
    let bMatch = m.pair[b] |
    let aNext = ^next[aList] |
    let bNext = ^next[bList] |
    aMatch != b and
    a != b and 
    {some l1, l2, l3, l4: List | 
    l1 in aList.*next and l2 in aList.*next and
    l1.person = b and l2.person = aMatch and
    l2 in ^next[l1] and  // a prefers b over aMatch
    l3 in bList.*next and l4 in bList.*next and
    l3.person = a and l4.person = bMatch and
    l4 in ^next[l3]  // b prefers a over bMatch
    }
}

run {
    init
    some m: Match | stable_match[m]
} for exactly 4 Person, exactly 8 List, exactly 1 Match

fun rankOf[p: Person, m: Match]: Int {
  let head = GroupA.priorities[p] + GroupB.priorities[p],
      target = m.pair[p] |
  #({ l: List | l in head.^next and l.person = target })
}

fun totalCost[m: Match]: Int {
    sum p: Person | rankOf[p, m]
}

fun groupCost[G: Group, m: Match]: Int {
    sum p: G.priorities.List | rankOf[p, m]
}

// Minimising the sum pf total cost
pred egalitarian[m1, m2: Match] {
    totalCost[m1] <= totalCost[m2]
}

// Minimize the absolute difference in total cost between groups
pred groupEqual[m1, m2: Match] {
    abs[groupCost[GroupA, m1] - groupCost[GroupB, m1]] <=
    abs[groupCost[GroupA, m2] - groupCost[GroupB, m2]]
}

// Minimize the maximum total cost of any group
pred balanced[m1, m2: Match] {
    max[groupCost[GroupA, m1], groupCost[GroupB, m1]] <=
    max[groupCost[GroupA, m2], groupCost[GroupB, m2]]
}

// Return the maximum individual regret (i.e. worst-case rank) among members of group G in matching m.
fun groupDegree[G: Group, m: Match]: Int {
    let rs = { r: Int | some p: G.priorities.List | r = rankOf[p, m] } |
    max[rs]
}

// Minimize the absolute difference between the worst-off agent in each group
pred regretEqual[m1, m2: Match] {
  abs[groupDegree[GroupA, m1] - groupDegree[GroupB, m1]] <=
  abs[groupDegree[GroupA, m2] - groupDegree[GroupB, m2]]
}


NotGroupEqual: run {
    init
    some m1, m2: Match |
        valid_match[m1] and valid_match[m2] and
        egalitarian[m1, m2] and not groupEqual[m1, m2]
} for exactly 6 Person, exactly 8 List, 2 Match
