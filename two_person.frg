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

one sig Mentor extends Group {}
one sig Mentee extends Group {}

pred init {
    Person in Mentor.priorities.List + Mentee.priorities.List // Every person is in either Mentor or Mentee
    no Mentor.priorities.List & Mentee.priorities.List // No one is in Mentor and Mentee
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

    -- Ensure at least one preference-list head is unique within its own group
    all disj p1, p2: Person | (p1 in Mentor.priorities.List and p2 in Mentor.priorities.List) implies
        (Mentor.priorities[p1]).person != (Mentor.priorities[p2]).person
    
    all disj q1, q2: Person | (q1 in Mentee.priorities.List and q2 in Mentee.priorities.List) implies
        (Mentee.priorities[q1]).person != (Mentee.priorities[q2]).person
}

run {init} for exactly 4 Person, 12 List, 1 Match

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

     all m: Match | some m.pair
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

StableMatch: run {
    init
    some m: Match | stable_match[m]
} for exactly 4 Person, exactly 8 List, 1 Match

// ----- metrics ------

fun rankOf[p: Person, m: Match]: Int {
  let head = Mentor.priorities[p] + Mentee.priorities[p],
      target = m.pair[p] |
  #({ l: List | l in head.^next and l.person = target })
}

fun totalCost[m: Match]: Int {
    sum p: Person | rankOf[p, m]
}

fun groupCost[G: Group, m: Match]: Int {
    sum p: G.priorities.List | rankOf[p, m]
}

// Return the maximum individual regret (i.e. worst-case rank) among members of group G in matching m.
fun groupDegree[G: Group, m: Match]: Int {
    let rs = { r: Int | all p: G.priorities.List | r = rankOf[p, m] } |
    max[rs]
}

// Return maximum individual regret (i.e. worst-case rank) 
fun maxDegree[m: Match]: Int {
    let rs = { r: Int | all p: Person | r = rankOf[p, m] } | 
    max[rs]
}

// Minimising the sum of total cost
pred isEgalitarian[m: Match] {
    let scores = { s: Int | all x: Match | s = totalCost[x]} |
    totalCost[m] = min[scores]
}

// Minimize the absolute difference in total cost between groups
pred isGroupEqual[m: Match] {
  let scores = { s: Int | all x: Match | s = abs[groupCost[Mentor, x] - groupCost[Mentee, x]]} |
    abs[groupCost[Mentor, m] - groupCost[Mentee, m]] = min[scores]
}

// Minimize the maximum total cost of any group
pred isBalanced[m: Match] {
  let scores = { s: Int | all x: Match | s = max [{ groupCost[Mentor, x] + groupCost[Mentee, x] }]} |
    max [{ groupCost[Mentor, m] + groupCost[Mentee, m] }] = min[scores]
}

// Minimize the absolute difference between the worst-off agent in each group
pred isRegretEqual[m: Match] {
  let scores = { s: Int | all x: Match | s = abs[groupDegree[Mentor, x] - groupDegree[Mentee, x]]} |
    abs[groupDegree[Mentor, m] - groupDegree[Mentee, m]] = min[scores]
}

// Minimize the the worst individual regret across all participants
pred isMinRegret[m: Match] {
  let scores = { s: Int | all x: Match | s = maxDegree[x]} |
    maxDegree[m] = min[scores]
}

Egalitarian: run {
    init
    all x: Match | stable_match[x] 
    some m: Match | isEgalitarian[m]
} for exactly 4 Person, exactly 8 List, 1 Match

GroupEqual: run {
    init
    all x: Match | stable_match[x] 
    some m: Match | isGroupEqual[m]
} for exactly 4 Person, exactly 8 List, 1 Match

RegretEqual: run {
    init
    all x: Match | stable_match[x]
    some m: Match | isRegretEqual[m]
} for exactly 4 Person, exactly 8 List, 1 Match

Balanced: run {
    init
    all x: Match | stable_match[x]
    some m: Match | isBalanced[m]
} for exactly 4 Person, exactly 8 List, 1 Match

MinRegret: run {
    init
    all x: Match | stable_match[x]
    some m: Match | isMinRegret[m]
} for exactly 4 Person, exactly 8 List, 1 Match