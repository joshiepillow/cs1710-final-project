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