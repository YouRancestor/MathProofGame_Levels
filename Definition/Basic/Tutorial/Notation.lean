

notation "ℕ" => Nat
macro "∀" "("a:ident "∈" t:term")""," p:term : term => do
  `(∀ ($a : $t), $p)
