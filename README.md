<!-- You should write a one-page README.md file describing how you structured your model and what your model proved. You can assume that anyone reading it will be familiar with your project proposal, but comprehensive documentation is always welcome. Here are some examples of points you might cover: -->

<!-- Did your goals change at all from your proposal? Did you realize anything you planned was unrealistic, or that anything you thought was unrealistic was doable?

What tradeoffs did you make in choosing your representation? What else did you try that didn’t work as well?

What assumptions did you make about scope? What are the limits of your model?

How should we understand an instance of your model and what your visualization shows (whether custom or default)? -->

# Mentor-Mentee Matching Model (Forge)

This model explores **stable matchings between Mentors and Mentees** using Forge, with a focus on evaluating fairness across multiple dimensions. It models preference lists, match structures, and fairness metrics, and provides experiments to reveal tradeoffs between them.

## Video Demo Link

[Watch the demo on Canva](https://www.canva.com/design/DAGm6cMctwU/Ony17Y-QIHgF_SmdqTL1oQ/edit?utm_content=DAGm6cMctwU&utm_campaign=designshare&utm_medium=link2&utm_source=sharebutton)

---

## Signatures

### `sig Person`

Represents a participant in the system. Each `Person` is either a `Mentor` or `Mentee`.

### `sig List`

A linked-list node used to represent preference rankings.

- `person`: the person this node refers to.
- `next`: optional reference to the next node.

### `abstract sig Group`

An abstract group (either `Mentor` or `Mentee`).

- `priorities`: maps each person in the group to their preference list head.

### `sig Match`

Represents a symmetric, bijective matching between people.

- `pair`: set of paired `Person -> Person`.

### `one sig Interval`

A temporal container for available `Person -> Person` pairs across time.

### `one sig Mentor`, `one sig Mentee`

Concrete subtypes of `Group`.

---

## Predicates

### `pred init`

Initializes a valid instance:

- Ensures persons belong to exactly one group.
- Assigns complete and disjoint preference lists.
- Ensures well-formed, non-redundant lists.

### `pred valid_match[m: Match]`

A valid match must:

- Be symmetric.
- Match every person to someone in the opposite group.
- Avoid self-matching.

### `pred stable_match[m: Match]`

A stable match has no blocking pair:

- No two unmatched individuals mutually prefer each other over their current match.

---

## Fairness Metrics

### `pred egalitarian[m1, m2]`

`m1` is better if it has **lower total cost** than `m2`.

- Reflects utilitarian ethics: maximizes total satisfaction across all participants.
- Ignores distributional fairness — may privilege majority preferences, as one group may be consistently worst off.

### `pred groupEqual[m1, m2]`

`m1` is better if the **group cost difference** between mentors and mentees is smaller than in `m2`.

- Prioritize equity between groups, especially when there is a power asymmetry between groups
- May equalize low ranks - neither group is well served.

### `pred balanced[m1, m2]`

`m1` is better if its **worst group cost** is no greater than `m2`'s.

- Focus on the worst off group not the difference, avoid scenarios where one group bears most of the burden
- Protecting one group at all costs may lower overall match satisfaction

### `pred regretEqual[m1, m2]`

`m1` is better if the **worst-case regret** in each group is more balanced than in `m2`.

- Emphasize fairness in worst-case experiences between groups, judged by relative group experience at the margins
- May lead to high overall regret just to equalize extremes.

### `pred minRegret[m1, m2]`

`m1` is better if the **maximum individual regret** is lower than in `m2`.

- Focus on the single person with the highest regret — minimizing how badly the worst-off person fares.
- Rawlsian fairness — the just society is the one that does best for the least advantaged.
- May favor outliers (e.g., one happy person and everyone else miserable)

---

## Matching Algorithm (Interval-Based Proposal Refinement)

This model implements a temporal version of the deferred acceptance algorithm using a relation called `Interval.intervals`, which evolves over time.

### How It Works

- Initially, all cross-group pairings are considered possible (`init` sets `Interval.intervals` to the full bipartite set).
- At each step (`update`), each person proposes to their top available choice, and each person keeps their best proposal (based on preferences).
- The algorithm removes all worse options from the intervals.
- This process continues until the set of considered options is constant (`constant`).
- When no further pruning is possible, the algorithm has converged to a final set of stable pairings.

### `one sig Interval`

A temporal relation used by the interval-based algorithm to model evolving proposals over time.

- `var intervals: set Person -> Person`: represents who is still being considered as a valid match by each person.

### Predicates

- `update`: One round of proposing and rejecting.
- `constant`: No more updates needed (fixpoint).
- `eventuallyConstant`: Fixpoint will eventually be reached.
- `groupOptimal[m, group]`: Asserts that a match `m` selects each person’s best partner at fixpoint.
- `associatedList[p, q]`: Helper to retrieve where `q` appears in `p`'s list.

### Formal Guarantees

- Termination is enforced with the `eventuallyConstant` property.
- The resulting set of intervals always encodes at least one stable matching.
- By fixing a group (e.g., `Mentor`) and always choosing each member's best available partner, we can recover the Mentor-optimal stable matching via `groupOptimal`.

---

## Design Rationale and Tradeoffs

### What tradeoffs did you make in choosing your representation? What else did you try that didn’t work as well?

We chose a linked list representation (`List`) for preference rankings because it allowed us to traverse through each person's priorities easily. We originally considered modeling preferences as `Person -> Int` mappings, but this representation lacked the natural ordering and relational functionality that we desired in ensuring valid preferences and matches. It wouldn't have allowed the `*` and `^` operators we used to check the completeness of the ranking.

To keep matchings symmetric, we modeled them as `pair: set Person -> Person` and added constraints in `valid_match` to enforce bidirectionality.

---

## Scope and Limitations

### What assumptions did you make about scope? What are the limits of your model?

We assume:

- Each person ranks all members of the opposite group (complete, strict preferences).
- Matchings are one-to-one and perfect (no unmatched individuals).
- Each group (`Mentor`, `Mentee`) has the same number of members.

This means the model does not support:

- Incomplete or partial rankings.
- Ties in preferences.
- Uneven group sizes or optional matchings.

In practice, this limits the model’s applicability to structured, idealized matching scenarios (e.g., mentorship pairings with symmetric expectations).

Additionally, we set out to compare how different fairness metrics (overall balance, worst-case protection, etc.) rate the same matching instance. At first we let Forge choose the priorities : set Person -> List relation freely. Forge’s default search often assigns identical preference lists to every person, so all stable matchings looked alike and the fairness metrics produced trivial ties.

To get meaningful variety, we added constraints forcing members of the same group to have a different preference order. That solved the trivial-tie problem, but because the lists are somewhat randommized, it also means every solver run uses a different preference profile. As a result it’s hard to line-up the fairness scores across runs and determine the best match since we are no longer evaluating the same underlying instance.

This reveals a limit in our modelling strategy. To claim that one particular matching is optimal according to a fairness metric, we needed to compare it against every other valid match. In Forge, this means considering all possible matchings explicitly in scope. But the number of possible matchings grows factorially with the number of people. As a result, it is much harder for Forge to run through and evaluate all matches as group sizes increase.

For practical testing we settled on a middle ground running experiments run with `6 Person` and `10 List` — enough to surface a few stable matchings while still being small enough for Forge’s solver to handle exhaustively.

---

## Goals and Original Proposal

### Did your goals change at all from your proposal? Did you realize anything you planned was unrealistic, or that anything you thought was unrealistic was doable?

While our original goal is to implement the interval algorithm and compare its performance to Gale-Shapley, we realized that this algorithm is symmetric in its interval selections, as both groups are proposing matches in line with their preferences. However, in extracting the final matches, the algorithm breaks this symmetry and returns a set of results that would ultimately favor one group. The set of considered pairings is symmetric but not the final results.

Additionally, one of our reach goals was to model matching roommates for rooms with triples, which we attempted at. But we realized that this goal was unrealistic given the time it took for Forge to run instances with more than 6 people. Run time ended up being a constraint for a large part of our exploration.

<!-- Our target goal is to compare the symmetric stable matching algorithm with Gale-Shapley and ensure that when one algorithm has a solution, the other must also have a solution. Furthermore, we want to determine a criteria for fairness and ensure that the symmetric stable matching algorithm is at least as fair as Gale-Shapley. We also want to know if the symmetric algorithm creates “better” stable matches than Gale-Shapley, i.e. by minimizing the average rank of each person’s partner in their preference list. -->

<!-- Our reach goal is finding sufficient and necessary criteria where the 3-roommates matching problem (or n-roommates) must have a stable match. Currently, this problem is unsolved, but we know there are instances where a stable match is possible and others where it is impossible, so we will attempt to find under which conditions each happens. -->

---

## 🧩 How to Understand the Model

### How should we understand an instance of your model and what your visualization shows?

Each instance consists of:

- A set of `Person`s split into `Mentors` and `Mentees`.
- Each person has a linked list of preferences over the opposite group.
- A `Match` assigning every person to a unique partner from the other group.

The custom visualization:

- Shows each person's preferences top-to-bottom in colored boxes.
- Highlights their actual match in a darker background.
- Draws matched pairs as colored circles below, showing group membership and partner connection.
- Displays fairness metrics
