
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro p,
  intro pb,
  have b : false := pb p,
  contradiction,
end

theorem doubleneg_elim : --⛤
  ¬¬P → P  :=
begin
  intro p1,
  by_contra hboom,
  have boom := p1 hboom,
  contradiction,
end

theorem doubleneg_law : --⛤
  ¬¬P ↔ P  :=
begin
  split,
  apply doubleneg_elim,
  apply doubleneg_intro,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro h,
  cases h with p q,
  right,
  exact p,
  left,
  exact q,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro h,
  cases h with p q,
  split,
  exact q,
  exact p,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro h,
  intro p,
  cases h with np q,
  have f := np p,
  contradiction,
  exact q,

end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro h,
  intro np,
  cases h with p q,
  have f := np p,
  contradiction,
  exact q, 
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro h1,
  intro h2,
  intro p,
  have q := h1 p,
  have f := h2 q,
  exact f,
end

theorem impl_as_contrapositive_converse : --⛤
  (¬Q → ¬P) → (P → Q)  :=
begin
  intro h1,
  intro p,
  by_contra hboom,
  have p2 := h1 hboom,
  have f := p2 p,
  exact f,
end

theorem contrapositive_law : --⛤
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  apply impl_as_contrapositive,
  apply impl_as_contrapositive_converse,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro h,
  have h2 : P∨¬P,
  right,
  intro p,
  have h3 : P∨¬P,
  left,
  exact p,
  have f : false := h h3,
  exact f,
  have f : false := h h2,
  exact f,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intro h1,
  intro h2,
  have pq : (P → Q),
  intro p,
  have f := h2 p,
  contradiction,
  have p := h1 pq,
  have f := h2 p,
  exact f,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro pq,
  intro h1,
  cases h1 with np nq,
  cases pq with p q,
  have f := np p,
  exact f,
  have f:= nq q,
  exact f,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro h1,
  intro h2,
  cases h1 with p q,
  cases h2 with np nq,
  have f := np p,
  exact f,
  have f := nq q,
  exact f,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro h1,
  split,
  intro p,
  have pq : (P ∨ Q),
  left,
  exact p,
  have f := h1 pq,
  exact f,
  intro q,
  have pq : (P ∨ Q),
  right,
  exact q,
  have f := h1 pq,
  exact f,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro h1,
  intro h2,
  cases h1 with np nq,
  cases h2 with p q,
  have f := np p,
  exact f,
  have f := nq q,
  exact f,
end

theorem demorgan_conj : --⛤
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro h,
  by_cases h2 : Q,
  right,
  intro p,
  apply h,
  split,
  exact p,
  exact h2,
  left,
  exact h2,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro h1,
  intro peq,
  cases peq with p q,
  cases h1 with nq np,
  have f := nq q,
  exact f,
  have f := np p,
  exact f,
end

theorem demorgan_conj_law : --⛤
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
  apply demorgan_conj,
  apply demorgan_conj_converse,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  apply demorgan_disj,
  apply demorgan_disj_converse,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro h,
  cases h with p qr,
  cases qr with q r,
  left,
  split,
  exact p,
  exact q,
  right,
  split,
  exact p,
  exact r,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro h,
  split,
  cases h with pq pr,
  cases pq with p q,
  exact p,
  cases pr with p r,
  exact p,
  cases h with pq pr,
  cases pq with p q,
  left,
  exact q,
  cases pr with p r,
  right,
  exact r,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro h,
  cases h with p qr,
  split,
  left,
  exact p,
  left,
  exact p,
  cases qr with q r,
  split,
  right,
  exact q,
  right,
  exact r,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro h,
  cases h with pq pr,
  cases pq with p q,
  left,
  exact p,
  cases pr with p r,
  left,
  exact p,
  right,
  split,
  exact q,
  exact r,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intro h,
  intro p,
  intro q,
  have pq : (P∧Q),
  split,
  exact p,
  exact q,
  have r : R := h pq,
  exact r,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intro h,
  intro pq,
  cases pq with p q,
  have qr := h p,
  have r := qr q,
  exact r,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro p,
  exact p,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro p,
  left,
  exact p,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro q,
  right,
  exact q,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro pq,
  cases pq with p q,
  exact p,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro pq,
  cases pq with p q,
  exact q,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  apply weaken_conj_right,
  intro p,
  split,
  exact p,
  exact p,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  intro h,
  cases h with p1 p2,
  exact p1,
  exact p2,
  apply weaken_disj_right,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intro h,
  intro x,
  intro p,
  apply h,
  existsi x,
  exact p,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro h1,
  intro h2,
  cases h2 with x px,
  have npx := h1 x,
  have f := npx px,
  exact f,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  := --⛤
begin
  intro h,
  by_contradiction h2,
  apply h,
  intro x,
  by_contradiction h3,
  apply h2,
  existsi x,
  exact h3,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro h1,
  intro h2,
  cases h1 with x npx,
  have px := h2 x,
  have f := npx px,
  exact f,
end

theorem demorgan_forall_law : --⛤
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
  apply demorgan_forall,
  apply demorgan_forall_converse,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
  apply demorgan_exists,
  apply demorgan_exists_converse,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intro h1,
  intro h2,
  cases h1 with x px,
  have npx := h2 x,
  have f : false := npx px,
  exact f,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intro h1,
  intro h2,
  cases h2 with x npx,
  have px := h1 x,
  have f : false := npx px,
  exact f,
end

theorem forall_as_neg_exists_converse : --⛤
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intro h1,
  intro x,
  by_contradiction h2,
  apply h1,
  existsi x,
  exact h2,
end

theorem exists_as_neg_forall_converse : --⛤
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  intro h1,
  by_contradiction h2,
  apply h1,
  intro x,
  intro px,
  apply h2,
  existsi x,
  exact px,
end

theorem forall_as_neg_exists_law : --⛤
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
  apply forall_as_neg_exists,
  apply forall_as_neg_exists_converse,
end

theorem exists_as_neg_forall_law : --⛤
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
  apply exists_as_neg_forall,
  apply exists_as_neg_forall_converse,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro h,
  cases h with u h2,
  cases h2 with pu qu,
  split,
  existsi u,
  exact pu,
  existsi u,
  exact qu,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro h1,
  cases h1 with u h2,
  cases h2 with pu qu,
  left,
  existsi u,
  exact pu,
  right,
  existsi u,
  exact qu,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro h,
  cases h with h2 h3,
  cases h2 with u pu,
  existsi u,
  left,
  exact pu,
  cases h3 with u qu,
  existsi u,
  right,
  exact qu,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro h1,
  split,
  intro u,
  have h2 := h1 u,
  cases h2 with pu qu,
  exact pu,
  intro u,
  have h2 := h1 u,
  cases h2 with pu qu,
  exact qu,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intro h,
  cases h with h1 h2,
  intro u,
  have pu := h1 u,
  have qu := h2 u,
  split,
  exact pu,
  exact qu,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intro h,
  intro u,
  cases h with h1 h2,
  have pu := h1 u,
  left,
  exact pu,
  have qu := h2 u,
  right,
  exact qu,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
