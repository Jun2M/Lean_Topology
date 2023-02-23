import topology.basic
import topology.bases
open topological_space
open set filter classical
variables {X : Type} [topological_space X] {A E F U V : set X} {B C : set(set X)}


-- some terms from the lectures
def cond_pt (A : set X) (x : X) := ∀ (N ∈ nhds x), (N ∩ A).nonempty
def cond_points (A : set X) := { x : X | cond_pt A x}
def limit_pt (A : set X) (x : X) := cond_pt (A ∩ {x}ᶜ) x
def limit_points (A : set X) := { x : X | limit_pt A x}


def lecture_closure (A : set X) := A ∪ limit_points A
def lecture_interior (A : set X) := {x : X | ∃ (N ∈ nhds x) (H: is_open N), N ⊆ A}


-- Bullet point 1
lemma subset_closed_subset_lecture_closure
  (A F : set X) (hAF : A ⊆ F) (hF : is_closed F) :
  lecture_closure A ⊆ F:=
begin
  intros x hA,
  cases hA,
  {exact hAF hA},
  {
    -- Re-using the complement neiborhood arguement used in proving lecture_closure_to_lean_closure

    -- since A is subset of F,
    have obvious_fact : A ∩ Fᶜ= ∅ := diff_eq_empty.mpr hAF,

    have more_specifically : Fᶜ ∩ (A ∩ {x}ᶜ) = ∅ ,
    -- since this is definately smaller than A ∩ Fᶜ
      rw set.inter_comm,
      apply diff_eq_empty.mpr,
      exact subset.trans (by finish) hAF,

    -- if x not in F, Fᶜ is an open neiborhood of x.
    -- Since x is a limit point of A,
    -- Fᶜ must contain an element of A but A ⊆ F. Contradiction.
    by_contradiction,

    have : Fᶜ ∈ nhds x := is_open.mem_nhds hF.is_open_compl h,
    cases hA Fᶜ this with N bad,
    finish,
  },
end

-- Bullet point 2
lemma open_subset_subset_interior 
  (U A : set X) (Uopen : is_open U) (UsubA : U ⊆ A) : U ⊆ lecture_interior A :=
begin
  intros x xinU,
  use U,
  apply and.intro,
  exact is_open.mem_nhds Uopen xinU,
  exact exists.intro Uopen UsubA,
end

-- Basis question
-- Exercise 2.1.6 part 2
-- Interestingly basis in Lean is defined 'using' B1 and B2 (and one other)
example (B : set(set X)) : is_topological_basis B → B.sUnion = set.univ ∧
  ∀ B1 B2 ∈ B, ∀ x ∈ B1 ∩ B2, (∃ B3 ∈ B, x ∈ B3 ∧ B3 ⊆ B1 ∩ B2):=
begin
  intros basis,
  split,
  exact basis.sUnion_eq,
  exact basis.exists_subset_inter,
end

-- Well, that was boring

structure is_lecture_basis (B : set(set X)) : Prop :=
  (open_sets : ∀ Bi ∈ B, is_open Bi)
  (construcable : ∀ (s : set X), is_open s → ∃ C ⊆ B, s = C.sUnion)

-- The real deal
example (B : set(set X)) : is_lecture_basis B → B.sUnion = set.univ ∧
  ∀ B1 B2 ∈ B, ∀ x ∈ B1 ∩ B2, (∃ B3 ∈ B, x ∈ B3 ∧ B3 ⊆ B1 ∩ B2):=
begin
  intros basis,
  split,
  {
    have Xisopen : is_open set.univ,      finish,
    have henceConstrucable :=             basis.construcable set.univ Xisopen,
    rcases henceConstrucable with ⟨ C, CinB, CconstX ⟩,

    -- univ = ⋃₀C ⊆ ⋃₀B ⊆ univ → ⋃₀B = univ
    have UCinUB : ⋃₀C ⊆ ⋃₀B :=          sUnion_mono CinB,
    have : ⋃₀B ⊆ set.univ :=            (⋃₀ B).subset_univ,
    rw ← CconstX at UCinUB,
    exact set.subset.antisymm this UCinUB,
  },
  {
    intros B1 hB1 B2 hB2 x hx,
    have Biopen := basis.open_sets,
    have B1open : is_open B1 :=           Biopen B1 hB1,
    have B2open : is_open B2 :=           Biopen B2 hB2,
    have inter_open :=                    is_open.inter B1open B2open,
    have henceConstrucable :=             basis.construcable (B1 ∩ B2) inter_open,
    rcases henceConstrucable with ⟨ C, CinB, CconstInter ⟩,
    rw CconstInter at hx,
    have Done : ∃ C1 ∈ C, x ∈ C1 :=          mem_sUnion.mp hx,

    rcases Done with ⟨ C1, C1inC, xinC1 ⟩,
    use C1,
    split,
    exact CinB C1inC,
    split,
    exact xinC1,
    rw CconstInter,
    exact subset_sUnion_of_mem C1inC,
  },
end

