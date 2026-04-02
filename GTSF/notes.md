What does the compilation from the source language to the poly. blame calculus look like?
We need to make sure it satisfies the static gradual guarantee.


F = λf:∀X.X→X. ΛY. λy:Y. f[Y] y
  = λf:∀X.X→X. ΛY. λy:Y. να:=Y. (f[α] @+(seal_α → seal_a)) y

F⋆ =  λf:⋆→⋆. ΛY. λy:Y. f[Y] y
   =? λf:⋆→⋆. ΛY. λy:Y. να:=Y. f @-(tag_α → tag_α) @+(seal_α → seal_α)  y

   The sealing and tagging on the domain is necessary to get from Y to ⋆,
   but what about the codomain? 
   Also, would we have to use a kind of bidirectional typing to have
   the type of y influence the compilation of the type application.


id : ∀X.X→X = ΛX. λx:X. x
id⋆ : ⋆ → ⋆ = λx:⋆. x

F id [ℕ] 42 -->* 42
F id⋆ [ℕ] 42 -->* 42


