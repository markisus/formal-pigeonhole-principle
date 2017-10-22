# formal-pigeonhole-principle
Formal proof of pigeonhole principle in Coq

The proof follows this outline:

Pigeonhole Principle: For all lists of natural numbers, if the sum of the numbers in the list exceeds the length of the list, then there is an element in the list that is greater than 1.

Proof by induction on size of the list.
Base case: the list is empty and the theorem doesn't apply.
Induction: Suppose the list is of the form cons(*a*, tail). 
Either *a* < 2, or *a* >= 2. If *a* < 2, then the induction hypothesis holds on the tail. 
If *a* >= 2, then *a* is the element we were looking for.
