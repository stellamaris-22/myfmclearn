section propositional

variable (P Q R : Prop)


------------------------------------------------
-- Double negation
------------------------------------------------

theorem doubleneg_intro :
    P → ¬ ¬ P  := by

  intro p np
  apply np p


theorem doubleneg_elim :
    ¬ ¬ P → P  := by

  intro nnp
  by_cases h : P
  exact h
  have boom : False := nnp h
  contradiction


theorem doubleneg_law :
    ¬ ¬ P ↔ P  := by

  constructor
  exact doubleneg_elim P
  exact doubleneg_intro P




------------------------------------------------
-- Commutativity of ∨,∧
------------------------------------------------

theorem disj_comm :
    (P ∨ Q) → (Q ∨ P)  := by
  intro poq
  rcases poq with (p|q)

  right
  exact p

  left
  exact q


theorem conj_comm :
    (P ∧ Q) → (Q ∧ P)  := by
  intro paq
  apply And.intro
  exact paq.right
  exact paq.left



------------------------------------------------
-- Interdefinability of →,∨
------------------------------------------------

theorem impl_as_disj_converse :
    (¬ P ∨ Q) → (P → Q)  := by
  intro npoq p
  rcases npoq with (np|q)

  have boom : False := np p
  contradiction

  exact q


theorem disj_as_impl :
    (P ∨ Q) → (¬ P → Q)  := by
  intro poq np
  rcases poq with (p|q)

  have boom :False := np p
  contradiction

  exact q


------------------------------------------------
-- Contrapositive
------------------------------------------------

theorem impl_as_contrapositive :
    (P → Q) → (¬ Q → ¬ P)  := by

  intro piq nq p
  apply nq (piq p)

theorem impl_as_contrapositive_converse :
    (¬ Q → ¬ P) → (P → Q)  := by

  intro nqinp p
  by_cases qnq : Q

  exact qnq

  have boom : False := (nqinp qnq) p
  contradiction

theorem contrapositive_law :
    (P → Q) ↔ (¬ Q → ¬ P)  := by

  constructor
  exact impl_as_contrapositive P Q
  exact impl_as_contrapositive_converse P Q


------------------------------------------------
-- Irrefutability of LEM[P]
------------------------------------------------

theorem lem_irrefutable :
    ¬ ¬ (P ∨ ¬ P)  := by
  intro n_ponp
  have ponp : (P ∨ ¬ P) := by
    right
    intro p
    have ponp : (P ∨ ¬ P) := by
      left
      exact p
    apply n_ponp ponp
  apply n_ponp ponp


------------------------------------------------
-- Peirce's law
------------------------------------------------

theorem peirce_law_weak :
    ((P → Q) → P) → ¬ ¬ P  := by
  intro piq_ip np
  have piq : P → Q := by
    intro p
    have boom: False := np p
    contradiction
  apply np (piq_ip piq)


------------------------------------------------
-- Linearity of →
------------------------------------------------

theorem impl_linear :
    (P → Q) ∨ (Q → P)  := by

  by_cases pnp : P

  right
  intro q
  exact pnp

  left
  intro p
  have boom : False := pnp p
  contradiction


------------------------------------------------
-- Interdefinability of ∨,∧
------------------------------------------------

theorem disj_as_negconj :
    P ∨ Q → ¬ (¬ P ∧ ¬ Q)  := by

  intro poq npanq
  rcases poq with ((p|q))
  apply npanq.left p
  apply npanq.right q

theorem conj_as_negdisj :
    P ∧ Q → ¬ (¬ P ∨ ¬ Q)  := by

  intro paq nponq
  rcases nponq with (np|nq)
  apply np paq.left
  apply nq paq.right


------------------------------------------------
-- De Morgan laws for ∨,∧
------------------------------------------------

theorem demorgan_disj :
    ¬ (P ∨ Q) → (¬ P ∧ ¬ Q)  := by


  intro n_poq
  apply And.intro

  intro p
  have poq : P ∨ Q := by
    left
    exact p
  apply n_poq poq

  intro q
  have poq : P ∨ Q := by
    right
    exact q
  apply n_poq poq

theorem demorgan_disj_converse :
    (¬ P ∧ ¬ Q) → ¬ (P ∨ Q)  := by

  intro npanq poq
  rcases poq with (p|q)

  apply npanq.left p
  apply npanq.right q

theorem demorgan_conj :
    ¬ (P ∧ Q) → (¬ Q ∨ ¬ P)  := by

  intro n_paq
  by_cases pnp : P

  by_cases qnq : Q

  have paq : P ∧ Q := by
    apply And.intro
    exact pnp
    exact qnq
  have boom : False := n_paq paq
  contradiction

  left
  exact qnq

  right
  exact pnp


theorem demorgan_conj_converse :
    (¬ Q ∨ ¬ P) → ¬ (P ∧ Q)  := by

  intro nqonp paq
  rcases nqonp with (nq|np)

  apply nq paq.right

  apply np paq.left


theorem demorgan_conj_law :
    ¬ (P ∧ Q) ↔ (¬ Q ∨ ¬ P)  := by

  constructor
  exact demorgan_conj P Q
  exact demorgan_conj_converse P Q

theorem demorgan_disj_law :
    ¬ (P ∨ Q) ↔ (¬ P ∧ ¬ Q)  := by
  constructor
  exact demorgan_disj P Q
  exact demorgan_disj_converse P Q


------------------------------------------------
-- Distributivity laws between ∨,∧
------------------------------------------------

theorem distr_conj_disj :
    P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R)  := by

    intro pa_qor
    rcases pa_qor.right with (q|r)

    left
    constructor
    exact pa_qor.left
    exact q

    right
    constructor
    exact pa_qor.left
    exact r


theorem distr_conj_disj_converse :
    (P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R)  := by

  intro paq_o_par
  rcases paq_o_par with (paq|par)

  constructor
  exact paq.left

  left
  exact paq.right

  constructor
  exact par.left
  right
  exact par.right


theorem distr_disj_conj :
    P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R)  := by

  intro po_qar
  rcases po_qar with (p|qar)
  constructor
  left
  exact p
  left
  exact p
  constructor
  right
  exact qar.left
  right
  exact qar.right

theorem distr_disj_conj_converse :
    (P ∨ Q) ∧ (P ∨ R) → P ∨ (Q ∧ R)  := by

  intro poq_a_por
  rcases poq_a_por.left with (p|q)

  left
  exact p

  rcases poq_a_por.right with (p|r)

  left
  exact p

  right
  constructor
  exact q
  exact r

------------------------------------------------
-- Currying
------------------------------------------------

theorem curry_prop :
    ((P ∧ Q) → R) → (P → (Q → R))  := by

  intro paqir p q
  have pq : P ∧ Q := by
    constructor
    exact p
    exact q
  apply paqir pq

theorem uncurry_prop :
    (P → (Q → R)) → ((P ∧ Q) → R)  := by

  intro piqir paq
  have qir : Q → R := piqir paq.left
  apply qir paq.right


------------------------------------------------
-- Reflexivity of →
------------------------------------------------

theorem impl_refl :
    P → P  := by
  intro h
  exact h


------------------------------------------------
-- Weakening and contraction
------------------------------------------------

theorem weaken_disj_right :
    P → (P ∨ Q)  := by
  intro p
  left
  exact p

theorem weaken_disj_left :
    Q → (P ∨ Q)  := by
  intro q
  right
  exact q

theorem weaken_conj_right :
    (P ∧ Q) → P  := by
  intro paq
  exact paq.left

theorem weaken_conj_left :
    (P ∧ Q) → Q  := by
  intro paq
  exact paq.right


------------------------------------------------
-- Idempotence of ∨,∧
------------------------------------------------

theorem disj_idem :
    (P ∨ P) ↔ P  := by
  constructor
  intro pop
  rcases pop with p|p
  exact p
  exact p
  intro p
  left
  exact p

theorem conj_idem :
    (P ∧ P) ↔ P := by
  constructor
  intro pap
  exact pap.left
  intro p
  constructor
  exact p
  exact p

------------------------------------------------
-- Bottom, Top
------------------------------------------------

theorem false_bottom :
    False → P := by
  intro boom
  contradiction

theorem true_top :
    P → True  := by
  intro p
  trivial


end propositional

----------------------------------------------------------------

section predicate

variable (U : Type)
variable (P Q : U → Prop)


------------------------------------------------
-- De Morgan laws for ∃,∀
------------------------------------------------

theorem demorgan_exists :
    ¬ (∃ x, P x) → (∀ x, ¬ P x)  := by
  intro nep
  intro a pa
  have ep : (∃ x, P x) := Exists.intro a pa
  apply nep ep




theorem demorgan_exists_converse :
    (∀ x, ¬ P x) → ¬ (∃ x, P x)  := by

  intro anp ep
  obtain ⟨a, ha⟩ := ep
  apply anp a ha



theorem demorgan_forall :
    ¬ (∀ x, P x) → (∃ x, ¬ P x)  := by

  intro nap
  by_cases enenp : ∃ (x : U), ¬P x
  exact enenp

  have ap : (∀ x, P x) := by -- Era p só app demorgan_exists com a Prop sendo ¬ P... mas n consegui
    intro a
    by_cases panpa : P a
    exact panpa
    have enp : (∃ x, ¬P x) := Exists.intro a panpa
    have boom : False := enenp enp
    contradiction

  have boom : False := nap ap
  contradiction

theorem demorgan_forall_converse :
    (∃ x, ¬ P x) → ¬ (∀ x, P x)  := by
  intro enp ap
  obtain ⟨a, ha⟩ := enp
  apply ha (ap a)


theorem demorgan_forall_law :
    ¬ (∀ x, P x) ↔ (∃ x, ¬ P x)  := by
  constructor
  exact demorgan_forall U P
  exact demorgan_forall_converse U P

theorem demorgan_exists_law :
    ¬ (∃ x, P x) ↔ (∀ x, ¬ P x)  := by
  constructor
  exact demorgan_exists U P
  exact demorgan_exists_converse U P

------------------------------------------------
-- Interdefinability of ∃,∀
------------------------------------------------

theorem exists_as_neg_forall :
    (∃ x, P x) → ¬ (∀ x, ¬ P x)  := by


  intro ep anp
  obtain ⟨a, pa⟩ := ep
  apply anp a pa

theorem forall_as_neg_exists :
    (∀ x, P x) → ¬ (∃ x, ¬ P x)  := by

  intro ap enp
  obtain ⟨a, npa⟩ := enp
  apply npa (ap a)



theorem forall_as_neg_exists_converse :
    ¬ (∃ x, ¬ P x) → (∀ x, P x)  := by

  intro nenp a
  by_cases panpa : P a
  exact panpa
  have enp : (∃ x, ¬ P x) := Exists.intro a panpa
  have boom: False := nenp enp
  contradiction


theorem exists_as_neg_forall_converse :
    ¬ (∀ x, ¬ P x) → (∃ x, P x)  := by
  intro nanp
  by_cases enep : ∃ (x : U), P x
  exact enep

  have anp : (∀ x, ¬P x) := by
    intro a
    by_cases panpa : P a
    have enp : (∃ x, P x) := Exists.intro a panpa
    have boom : False := enep enp
    contradiction
    exact panpa

  have boom : False := nanp anp
  contradiction


theorem forall_as_neg_exists_law :
    (∀ x, P x) ↔ ¬ (∃ x, ¬ P x)  := by
  constructor
  exact forall_as_neg_exists U P
  exact forall_as_neg_exists_converse U P


theorem exists_as_neg_forall_law :
    (∃ x, P x) ↔ ¬ (∀ x, ¬ P x)  := by
  constructor
  exact exists_as_neg_forall U P
  exact exists_as_neg_forall_converse U P


------------------------------------------------
--  Distributivity between quantifiers
------------------------------------------------

theorem exists_conj_as_conj_exists :
    (∃ x, P x ∧ Q x) → (∃ x, P x) ∧ (∃ x, Q x)  := by
  intro epaq
  obtain ⟨a, paaqa⟩ := epaq
  constructor

  apply Exists.intro a paaqa.left
  apply Exists.intro a paaqa.right

theorem exists_disj_as_disj_exists :
    (∃ x, P x ∨ Q x) → (∃ x, P x) ∨ (∃ x, Q x)  := by
  intro epoq
  obtain ⟨a, paoqa⟩ := epoq
  rcases paoqa with pa|qa
  left
  apply Exists.intro a pa
  right
  apply Exists.intro a qa

theorem exists_disj_as_disj_exists_converse :
    (∃ x, P x) ∨ (∃ x, Q x) → (∃ x, P x ∨ Q x)  := by
  intro epoeq
  rcases epoeq with ep|eq

  obtain ⟨a, pa⟩ := ep
  have paoqa : P a ∨ Q a := by
    left
    exact pa
  apply Exists.intro a paoqa

  obtain ⟨b, qb⟩ := eq
  have pboqb : P b ∨ Q b := by
    right
    exact qb
  apply Exists.intro b pboqb


theorem forall_conj_as_conj_forall :
    (∀ x, P x ∧ Q x) → (∀ x, P x) ∧ (∀ x, Q x)  := by

  intro apaq
  constructor
  intro a
  have paaqa : P a ∧ Q a := apaq a
  exact paaqa.left

  intro b
  have pbaqb : P b ∧ Q b := apaq b
  exact pbaqb.right

theorem forall_conj_as_conj_forall_converse :
    (∀ x, P x) ∧ (∀ x, Q x) → (∀ x, P x ∧ Q x)  := by
  intro apaaq b
  constructor
  exact apaaq.left b
  exact apaaq.right b

theorem forall_disj_as_disj_forall_converse :
    (∀ x, P x) ∨ (∀ x, Q x) → (∀ x, P x ∨ Q x)  := by
  intro apoaq b
  rcases apoaq with ap|aq
  left
  exact ap b

  right
  exact aq b


end predicate

------------------------------------------------

section bonus

------------------------------------------------
--  Drinker's paradox
------------------------------------------------

variable (D : U → Prop)

-- There is a person p such that:
-- if p drinks, then everybody drinks
-- p: «person»
-- D x: «x drinks»
theorem drinker :
    ∃ p, (D p → ∀ x, D x)  := by


  by_cases endnend : ∃ p, ¬D p

  obtain ⟨a, dna⟩ := endnend
  apply Exists.intro a
  intro da
  have boom : False := dna da
  contradiction

  have ad : ∀ x, D x := by

  -- forall_as_neg_exists_converse

    intro b
    by_cases dbndb : D b
    exact dbndb
    have enp : (∃ x, ¬ D x) := Exists.intro b dbndb
    have boom: False := endnend enp
    contradiction

--i need to introduce a guy...
  by_cases edned : ∃ x, D x

  obtain ⟨c, dc⟩ := edned

  apply Exists.intro c
  intro dc2
  exact ad

  have and : ∀ x, ¬ D x := by
    intro k dk
    have ed : (∃ x, D x) := Exists.intro k dk
    apply edned ed


  /-
  Maybe not provable cause i cant be sure there *is* a guy in the bar...?
  But wouldnt it mean by vacuity everyone drinks, satisfying the implication?
  But i also wont have a guy to point to...
  goddammit.

  if i could have *one* guy in U i could easily prove it, but i cant be sure
  Id just apply al & and to the guy and boom

  The empty bar really is a loophole

  i love proof assistants.
  -/

  sorry




------------------------------------------------
--  Russell's paradox
------------------------------------------------

variable (S : U → U → Prop)

-- It is impossible to have a barber b such that
-- b shaves exactly those people who do not shave themselves
-- b: «barber»
-- S x y: «x shaves y»
theorem russell :
    ¬ ∃ b, ∀ x, (S b x ↔ ¬ S x x)  := by
  intro easiffns
  obtain ⟨a, asaiffns⟩ := easiffns
  have saaiffnsaa : S a a ↔ ¬S a a := asaiffns a
  by_cases saansaa : S a a

  have nsaa : ¬ S a a := saaiffnsaa.mp saansaa
  have boom : False := nsaa saansaa
  exact boom

  have saa : S a a := saaiffnsaa.mpr saansaa
  have boom : False := saansaa saa
  exact boom

end bonus


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
    (∀ x, P x ∨ Q x) → (∀ x, P x) ∨ (∀ x, Q x)  := by
  sorry

theorem exists_conj_as_conj_exists_converse :
    (∃ x, P x) ∧ (∃ x, Q x) → (∃ x, P x ∧ Q x)  := by
  sorry

---------------------------------------------- -/
