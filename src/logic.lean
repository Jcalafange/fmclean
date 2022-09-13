section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intros h h2,
  apply h2,
  contradiction,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro h,
  by_cases h : P,
  assumption,
  contradiction,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  intro h,
  by_cases h: P,
  assumption,
  contradiction,
  intros h h2,
  contradiction,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro h,
  cases h with hp hq,
  right,
  exact hp,
  left,
  assumption,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro h,
  cases h with hp hq,
  split,
  assumption,
  exact hp,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intros h,
  cases h with h1 h2,
  contradiction,
  intro h',
  assumption,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro h,
  cases h with h' h'',
  contradiction,
  intro nh,
  assumption,

end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intros h h2 h3,
  have hq : Q := h h3,
  contradiction,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intros h h2,
  by_cases h3 : Q,
  exact h3,
  have nhp : ¬P := h h3,
  contradiction,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  intros h h2 h3,
  have hq : Q := h h3,
  contradiction,
  intros h' h'',
  by_cases h3 : Q,
  exact h3,
  have nhp : ¬P := h' h3,
  contradiction,
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
  intro galinha,
  have h'' : P∨¬P,
  left,
  assumption,
  apply h h'',
  apply h h2,
  
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
   intros h h',
  have h''' : (P → Q),
  intro h'',
  contradiction,
  have peixe : P := h h''',
  contradiction,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intros h h',
  cases h',
  cases h,
  contradiction,
  contradiction,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intros h h',
  cases h,
  cases h',
  contradiction,
  contradiction,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intros h,
  split,
  intro h',
  have pvq : P∨Q,
  left,
  assumption,
  contradiction,
  intro h'',
  have pvq' : P∨Q,
  right,
  assumption,
  contradiction,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intros h galinha,
  cases galinha with hp hq,
  cases h with np nq,
  contradiction,
  cases h with np nq,
  contradiction,

end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro h,
  by_cases hq: Q,
  right,
  intro hp,
  have galinha : (P∧Q),
  split,
  assumption,
  assumption,
  contradiction,
  left,
  assumption,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro h,
  intro galinha,
  cases galinha with nq np,
  cases h with noq nop,
  contradiction,
  contradiction,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
  intro h,
  by_cases hq: Q,
  right,
  intro hp,
  have galinha : (P∧Q),
  split,
  assumption,
  assumption,
  contradiction,
  left,
  assumption,
  intro h,
  intro galinha,
  cases galinha with nq np,
  cases h with noq nop,
  contradiction,
  contradiction,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  exact demorgan_disj P Q,
  exact demorgan_disj_converse P Q,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro h,
  cases h with p galinha,
  cases galinha with q r,
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
  cases h with galinha hr,
  cases galinha with p q,
  split,
  exact p,
  left,
  exact q,
  cases hr with pp r,
  split,
  exact pp,
  right,
  exact r,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro h,
  cases h with p galinha,
  split,
  left,
  exact p,
  left,
  exact p,
  cases galinha with q r,
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
  cases h with galinha hr,
  cases galinha with p q,
  left,
  exact p,
  cases hr with p r,
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
  intro hp,
  intro hq,
  have galinha : P∧Q,
  split,
  exact hp,
  exact hq,
  apply h galinha,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intro hpqr,
  intro galinha,
  cases galinha with p q,
  apply hpqr p,
  exact q,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro hp,
  exact hp,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro peixe,
  left,
  exact peixe,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro quadrinhos,
  right,
  exact quadrinhos,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro h,
  cases h with p q,
  exact p,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro h,
  cases h with p q,
  exact q,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro hp,
  cases hp with p pp,
  exact p,
  intro galinha,
  split,
  exact galinha,
  exact galinha,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  intro h,
  cases h with p pp,
  exact p,
  exact pp,
  intro hp,
  left,
  exact hp,
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
  intro he,
  intro x,
  intro p,
  apply he,
  existsi x,
  exact p,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro ha,
  intro he,
  cases he with t agate,
  exact (ha t) agate,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  rw contrapositive_law,
  rw doubleneg_law,
  intro piada,
  intro a,
  by_contradiction hboom,
  apply piada,
  existsi a,
  exact hboom,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro he,
  intro ha,
  cases he with t ht,
  have pt : P t := ha t,
  contradiction,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
  exact demorgan_forall U P,
  exact demorgan_forall_converse U P,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
  exact demorgan_exists U P,
  exact demorgan_exists_converse U P,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intro he,
  intro ha,
  cases he with x he,
  have nhp : ¬P x := ha x,
  contradiction,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intro ha,
  intro he,
  cases he with x he,
  have hp : P x := ha x,
  contradiction, 
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intro he,
  intro x,
  by_contradiction px,
  apply he,
  existsi x,
  exact px,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  rw contrapositive_law,
  intro piada,
  intro piadinha,
  apply piadinha,
  intro t,
  intro spidermen,
  apply piada,
  existsi t,
  exact spidermen,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
  exact forall_as_neg_exists U P,
  exact forall_as_neg_exists_converse U P,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
  exact exists_as_neg_forall U P,
  exact exists_as_neg_forall_converse U P,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro h,
  cases h with a ha,
  cases ha with hp hq,
  split,
  --Parte P(x)
  existsi a,
  exact hp,
  --Parte Q(x)
  existsi a,
  exact hq,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro h,
  cases h with a ha,
  cases ha with Pa Qa,
  left,
  existsi a,
  exact Pa,
  right,
  existsi a,
  exact Qa,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro h,
  cases h with Pa Qa,
  cases Pa with a ha,
  existsi a,
  left,
  exact ha,
  cases Qa with a ha,
  existsi a,
  right,
  exact ha,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro h,
  split,
  intro a,
  have ha : P a ∧ Q a := h a,
  cases ha with hl hr,
  exact hl,
  intro a,
  have ha : P a ∧ Q a := h a,
  cases ha with hl hr,
  exact hr,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intro h,
  intro a,
  cases h with hl hr,
  split,
  have hp : P a := hl a,
  exact hp,
  have hq : Q a := hr a,
  exact hq,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intro h,
  intro a,
  cases h with hl hr,
  have hp : P a := hl a,
  left,
  exact hp,
  have hq : Q a := hr a,
  right,
  exact hq,
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
