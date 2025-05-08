#lang forge/temporal

open "algorithms.frg"

test suite for interval {
    // New interval is always contained in old interval
    assert {
        init 
        always update
        not always {Interval.interval' in Interval.interval}
    } is unsat

    // Everyone always has someone in their interval
    assert {
        init 
        always update
        not always {all p: Person | some (p -> Person) & Interval.interval}
    } is unsat

    // Everyone is always in someone else's interval
    assert {
        init 
        always update
        not always {all p: Person | some (Person -> p) & Interval.interval}
    } is unsat

    // Check that algorithm always terminates eventually
    assert { init (always update) } is sufficient for eventuallyConstant
}