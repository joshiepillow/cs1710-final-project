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
}

run { init } for exactly 4 Person, exactly 8 List