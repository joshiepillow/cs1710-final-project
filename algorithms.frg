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

// Check that algorithm always terminates eventually
assert { init (always update) } is sufficient for eventuallyConstant

// Using the algorithm's output, pick the GroupA or GroupB-optimal matching
pred groupOptimal[m: Match, group: Group] {
    let s = {p: group.priorities.List, q: Person | q in max[p, Interval.intervals[p]]} |
        always {constant implies {m.pair = s + ~s}}
}

run {
    init
    always update
    some m: Match | groupOptimal[m, GroupA]
} for exactly 4 Person, exactly 8 List, 1 Match

// Require no identical matchings. Necessary to force all matchings to exist
pred noIdenticalMatchings {
    no disj m1, m2: Match | m1.pair = m2.pair
}

fun rankOf[p: Person, m: Match]: Int {
  let head = GroupA.priorities[p] + GroupB.priorities[p],
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

// There are only 24 distinct matchings for 2 groups of 4 people
assert {
    init
    {all m: Match | valid_match[m]}
    noIdenticalMatchings
} is unsat for exactly 8 Person, exactly 32 List, exactly 25 Match
assert {
    init
    {all m: Match | valid_match[m]}
    noIdenticalMatchings
} is sat for exactly 8 Person, exactly 32 List, exactly 24 Match

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
            (p1 in GroupA.priorities.List and p2 in GroupB.priorities.List) or
            (p1 in GroupB.priorities.List and p2 in GroupA.priorities.List)

     all l: List | some l.person
}

// There is always a best matching
assert { 
    init
    all m: Match | valid_match[m]
    noIdenticalMatchings
} is sufficient for existsBest for exactly 4 Person, exactly 8 List, exactly 2 Match

// Check that the best matching is necssarily stable
assert {
    init 
    all m: Match | valid_match[m]
    noIdenticalMatchings
    some m: Match | {bestMatching[m] and not stable_match[m]}
} is unsat for exactly 4 Person, exactly 8 List, exactly 2 Match

// Check that the best matching is necessarily in the interval
assert {
    init 
    always update
    all m: Match | valid_match[m]
    noIdenticalMatchings
    some m: Match | {bestMatching[m] and m.pair not in Interval.intervals}
} is unsat for exactly 4 Person, exactly 8 List, exactly 2 Match

// Check that the best matching is not always the GroupA or GroupB-optimal matching
assert {
    init 
    always update
    all m: Match | valid_match[m]
    noIdenticalMatchings
    some m: Match | {bestMatching[m] and not groupOptimal[m, GroupA] and not groupOptimal[m, GroupB]}
} is sat for exactly 4 Person, exactly 8 List, exactly 2 Match