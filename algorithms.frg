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

one sig Mentor extends Group {}
one sig Mentee extends Group {}

pred init {
    Person in Mentor.priorities.List + Mentee.priorities.List // Every person is in either Mentor or Mentee
    no Mentor.priorities.List & Mentee.priorities.List // No one is in Mentor in Mentee
    #{Mentor.priorities} = #{Mentee.priorities} // Same size
    all p: Person {
        // Only one ranking per person
        lone (p -> List) & Mentor.priorities
        lone (p -> List) & Mentee.priorities

        // Every member of each group ranks all other members from the other group
        p in Mentor.priorities.List implies (Mentor.priorities[p]).*next.person = Mentee.priorities.List
        p in Mentee.priorities.List implies (Mentee.priorities[p]).*next.person = Mentor.priorities.List
    }
    all l: List {
        l.person not in l.^next.person // No ranking includes the same person twice
        l in Person.(Group.priorities).*next // No dangling irrelevant lists
    }
    // Initially all members of Mentor are considered by all members of Mentee and vice versa
    Interval.intervals = Mentor.priorities.List -> Mentee.priorities.List + Mentee.priorities.List -> Mentor.priorities.List
}

pred stable_match[m: Match] {
  valid_match[m]

  no a, b: Person |
    let aList = Mentor.priorities[a] + Mentee.priorities[a] |
    let bList = Mentor.priorities[b] + Mentee.priorities[b] |
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

// Get the associated list for person q in p's priorities
fun associatedList[p: Person, q: Person]: one List {
    {l: List | l in (Group.priorities[p]).*next and l.person = q}
}

// Return p's top choice among set s
fun max[p: Person, s: set Person]: one Person {
    {q: Person | q in s and s in (associatedList[p, q]).*next.person}
}

// Interval algorithm's update rule
pred update {
    let top = {p: Person, q: Person | q in max[p, Interval.intervals[p]]} |
    let best = {q: Person, bestP: Person | bestP in max[q, {p: Person | q = top[p]}]} | {
        Interval.intervals' = {q: Person, p: Person | p in Interval.intervals[q] and p not in (associatedList[q, best[q]]).^next.person} - {p: Person, q: Person | q in top[p] and p not in Interval.intervals[q]}
    }
}

// Update does nothing; algorithm is finished
pred constant {
    Interval.intervals' = Interval.intervals
}

pred eventuallyConstant {
    eventually constant
}

// Using the algorithm's output, pick the Mentor or Mentee-optimal matching
pred groupOptimal[m: Match, group: Group] {
    let s = {p: group.priorities.List, q: Person | q in max[p, Interval.intervals[p]]} |
        always {constant implies {m.pair = s + ~s}}
}

run {
    init
    always update
    some m: Match | groupOptimal[m, Mentor]
} for exactly 6 Person, exactly 18 List, 1 Match

// Require no identical matchings. Necessary to force all matchings to exist
pred noIdenticalMatchings {
    no disj m1, m2: Match | m1.pair = m2.pair
}

fun rankOf[p: Person, m: Match]: Int {
  let head = Mentor.priorities[p] + Mentee.priorities[p],
      target = m.pair[p] |
  #({ l: List | l in head.^next and l.person = target })
}

fun totalCost[m: Match]: Int {
    sum p: Person | rankOf[p, m]
}

// Minimising the sum pf total cost
pred egalitarian[m1, m2: Match] {
    totalCost[m1] <= totalCost[m2]
}


// require that m is best matching
pred bestMatching[m: Match] {
    all other: Match | egalitarian[m, other]
}

// There are only 6 distinct matchings for 2 groups of 3 people
assert {
    init
    {all m: Match | valid_match[m]}
    noIdenticalMatchings
} is unsat for exactly 8 Person, 8 List, exactly 25 Match
assert {
    init
    {all m: Match | valid_match[m]}
    noIdenticalMatchings
} is sat for exactly 8 Person, 8 List, exactly 24 Match

// There exists a best matching
pred existsBest {
    some m: Match | bestMatching[m]
}

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
            (p1 in Mentor.priorities.List and p2 in Mentee.priorities.List) or
            (p1 in Mentee.priorities.List and p2 in Mentor.priorities.List)

     all l: List | some l.person
}

// There is always a best matching
assert { 
    init
    all m: Match | valid_match[m]
    noIdenticalMatchings
} is sufficient for existsBest for exactly 4 Person, exactly 8 List, exactly 2 Match

// There exists a stable best matching
assert {
    init 
    all m: Match | valid_match[m]
    noIdenticalMatchings
    not (some m: Match | {bestMatching[m] and stable_match[m]})
} is unsat for exactly 4 Person, exactly 8 List, exactly 2 Match

// There exists a best matching in the interval
assert {
    init 
    always update
    all m: Match | valid_match[m]
    noIdenticalMatchings
    not (some m: Match | {bestMatching[m] and always m.pair in Interval.intervals})
} is unsat for exactly 4 Person, exactly 8 List, exactly 2 Match

// Check that the best matching is not always the Mentor or Mentee-optimal matching
assert {
    init 
    always update
    all m: Match | valid_match[m]
    noIdenticalMatchings
    some m: Match | {bestMatching[m] and not groupOptimal[m, Mentor] and not groupOptimal[m, Mentee]}
} is sat for exactly 4 Person, exactly 8 List, exactly 2 Match