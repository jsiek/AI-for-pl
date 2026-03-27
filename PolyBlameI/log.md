# March 27, 2026

Ran into a problem with the imprecision side conditions and type
substitution.

In the notes we have:

(1) a ∉ dom(Σ) guarantees we don't have both id_α and (seal_α;p)
    in the same imprecision judgement.

(2) G ∉ dom(Σ) guarantees we don't have both (id_α;tag_α) and (seal_α;p)
    in the same imprecision judgement.

Suppose we are substituting X for α in an imprecision (e.g., triggered
by the application of a type abstraction), but the imprecision already
has seal_α inside. The substitution will turn id_X into id_α and then
the above invariant will be violated.

να:=ℕ. (((ΛX. (λx:X. 0) @ −(id_X → seal_α)) α) @ +(seal_α → seal_α))
-->
να:=ℕ. (((λx:α. 0) @ −(id_α → seal_α)) @ +(seal_α → seal_α))



