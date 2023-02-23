import topology.basic
open topological_space
open set filter classical
variables {X : Type} [topological_space X] {A E F U V : set X}


-- Challenge Accepted

-- defining some terms to avoid mess (not that this file is not mess but it helps)
def lecture_closure (A : set X) := A ∪ {x : X | ∀(N ∈ nhds x) (H: is_open N), A ∩ N ≠ ∅}
def lecture_interior (A : set X) := {x : X | ∃ (N ∈ nhds x) (H: is_open N), N ⊆ A}

-- Good old antisymm method for showing equivalence (i.e. a ⊆ b ∧ b ⊆ a → a = b)

lemma lecture_interior_to_lean_interior : lecture_interior A ⊆ interior A :=
begin
  -- ∀ x in lecture_interior, contained in open neighborhood N in A, N is subset of maximal open set in A
  intros x xinlec,
  rcases xinlec with ⟨ N, Nnhd, Nopen, nhdinA ⟩,
  apply set.mem_sUnion_of_mem (mem_of_mem_nhds Nnhd) (and.intro Nopen nhdinA),
end

lemma lean_interior_to_lecture_interior : interior A ⊆ lecture_interior A :=
begin
  -- x in lean_interior means there exist an open set in A containing x. Call that set N. Done.
  unfold interior,
  intros x lean_interior,
  rw set.mem_sUnion at lean_interior,
  rcases lean_interior with ⟨ t, ht, xint ⟩,
  use t,
  split,
  {
    rw mem_nhds_iff,
    use t,
    split,
    refl,
    exact and.intro ht.left xint,
  },
  {
    split,
    exact ht.left,
    exact ht.right,
  },
end

-- antisymm to combine the above result
lemma interior_equivalence : interior A = lecture_interior A :=
begin
  apply set.subset.antisymm,
  exact lean_interior_to_lecture_interior,
  exact lecture_interior_to_lean_interior,
end

-- Now the turn for equivalence of closure
lemma lecture_closure_to_lean_closure (x : X): x ∈ lecture_closure A → x ∈ closure A :=
begin
  -- if x in A, easy since all closed set including A includes x,
  -- if x is limit point of A, if x is not in lean_closure and hence there is a closed set t not containing x,
  -- tᶜ is an open set containing x so (since x is limit point of A), tᶜ has element of A while A ⊆ t.
  intro lec_clo,
  cases lec_clo;
  unfold closure;
  rw set.mem_sInter;
  intros t ht,
  {exact set.mem_of_mem_of_subset lec_clo ht.right,},
  {
    by_contradiction,
    have tclosed := ht.left,
    rw ← is_open_compl_iff at tclosed,
    have := lec_clo tᶜ ,
    apply lec_clo tᶜ (is_open.mem_nhds tclosed (set.mem_compl h)) tclosed,
    rw [← set.subset_empty_iff, ← set.inter_compl_self t],
    exact set.inter_subset_inter_left tᶜ ht.right,
  },
end

-- I don't seem to be able to prove lean_closure_to_lecture_closure directly so 
lemma useful : (lecture_interior Aᶜ)ᶜ ⊆ lecture_closure A :=
begin
  unfold lecture_interior,
  rw set.compl_set_of,
  push_neg,
  intros x b,
  cases classical.em (x ∈ A),
  {left,
    exact h},
  {
    right,
    intros N Nnhd Nopen,
    rw [set.inter_comm, set.ne_empty_iff_nonempty, ← compl_compl A, set.inter_compl_nonempty_iff],
    exact b N Nnhd Nopen,
  },
end

-- Now that I have the above (definitionaly) useful lemma I can prove this very easily
lemma lean_closure_to_lecture_closure (x : X): x ∈ closure A → x ∈ lecture_closure A :=
begin
  rw closure_eq_compl_interior_compl,
  rw interior_equivalence,
  intro a,
  exact useful a,
end

-- Antisymm for the last time and DONE!!!!!!!!!!!!!!!!!!!!!!!!!!
theorem closure_equivalence : closure A = lecture_closure A :=
begin
  apply set.subset.antisymm,
  exact lean_closure_to_lecture_closure,
  exact lecture_closure_to_lean_closure,
end

------------------------------------------------------------------------------------

-- Example 2.1.1.
example : is_closed F → A ⊆ F → closure A ⊆ F :=
begin
  intros Fclosed AinF,
  unfold closure,
  /- 
  this is not how closure is defined in the module.
  smallest closed set containing A? I guess it kinda makes sense. 
  -/
  let T := {t : set X | is_closed t ∧ A ⊆ t},
  have : F ∈ T,
  apply and.intro,
  exact Fclosed,
  exact AinF,
  /-
  Since F is one of the closed set containing A,
  intersections of sets in T (including F) is obviously a subset of F.
  -/
  apply sInter_subset_of_mem,
  exact this,
end

example : is_open U → U ⊆ A → U ⊆ interior A :=
begin
  intros Uopen UinA,
  unfold interior,
  -- A° = largest open set within A?
  let T := {t : set X | is_open t ∧ t ⊆ A},
  have h1 : U ∈ T,
    exact and.intro Uopen UinA,
  -- I would assume there is a equivalent thing but I don't seem to be able to find it so,
  apply set.subset_sUnion_of_subset T U,
  {by refl},
  {exact h1},
end

