import topology.basic
import topology.maps
import topology.homeomorph
open topological_space
open set filter classical
variables {X Y : Type} [topological_space X] [topological_space Y] [nonempty X] [nonempty Y] {A E F U V : set X}
open function

/-Exercise 2.2.2. [⋆] Show that the following are equivalent for a continuous map 𝑓 ∶ 𝑋 → 𝑌
between spaces (𝑋, 𝒪𝑋) and (𝑌, 𝒪𝑌).
(i) 𝑓 ∶ 𝑋 → 𝑌 is a homeomorphism.
(ii) 𝑓 is an open bijection.
(iii) 𝑓 is a closed bijection.
♣

Exercise 2.2.7. [+] Let 𝒮 be the collection from Exercise 2.2.6. Show that the collection
𝒮𝑛 = {𝑝ᵢ⁻¹(𝑆) ∶ all 𝑆 ∈ 𝒮 and 1 ≤ 𝑖 ≤ 𝑛}
where the 𝑝𝑖 are the 𝑛 coordinate projections, is a subbase for the standard topology on ℝ𝑛
. ♣-/


-- definitions
-- open function is defined the same way with the name is_open_map
-- the same for closed function
def inverse {X Y : Type} (f : X → Y) (f' : Y → X) := 
right_inverse f f' ∧ left_inverse f f'
def is_homeomorphism (f : X → Y) := 
function.bijective f ∧ continuous f ∧ ∃ (f' : Y → X) (H : inverse f f'), continuous f'
def is_hom (f : X → Y) := 
continuous f ∧ ∃ (f' : Y → X), inverse f f' ∧ continuous f'


-- I am very angry at how inverse function is coded in Lean
-- Are the following lemmas not in lean or am I blind???

lemma inv_imp_bij {X' Y' : Type} (f : X' → Y') (f' : Y' → X'):
inverse f f' → function.bijective f:=
begin
  intro f'inv,
  refine function.bijective_iff_has_inverse.mpr _,
  use f',
  exact f'inv,
end

lemma linv_imp_rinv_swap {X' Y' : Type} (f : X' → Y') (f' : Y' → X') : 
function.left_inverse f f' → function.right_inverse f' f :=
begin
  intros linv x,
  exact linv x,
end

lemma rinv_imp_linv_swap {X' Y' : Type} (f : X' → Y') (f' : Y' → X') : 
function.right_inverse f f' → function.left_inverse f' f :=
begin
  intros rinv x,
  exact rinv x,
end

lemma rinv_iff_linv_swap {X' Y' : Type} (f : X' → Y') (f' : Y' → X') :
function.right_inverse f f' ↔ function.left_inverse f' f :=
begin
  split,
  exact rinv_imp_linv_swap f f',
  exact linv_imp_rinv_swap f' f,
end

lemma inv_swap {X' Y' : Type} (f : X' → Y') (f' : Y' → X') : inverse f f' → inverse f' f :=
begin
  intros h,
  split,
  exact rinv_imp_linv_swap f' f h.right,
  exact linv_imp_rinv_swap f' f h.left,
end

lemma inv_symm {X' Y' : Type} (f : X' → Y') (f' : Y' → X') : inverse f f' ↔ inverse f' f :=
begin
  split,
  have := inv_swap f f',
  exact this,
  have := inv_swap f' f,
  exact this,
end

lemma hom_homeo_equiv (f : X → Y) : is_hom f ↔ is_homeomorphism f :=
begin
  split,
  {
    intros fhom,
    rcases fhom with ⟨ fcont, f', f'inv, f'cont ⟩ ,
    split,
    exact inv_imp_bij f f' f'inv,
    split,
    exact fcont,
    use f',
    exact ⟨f'inv, f'cont⟩,
  },
  {
    intros fhomeo,
    rcases fhomeo with ⟨ fbij, fcont, f', f'inv, f'cont ⟩ ,
    split,
    exact fcont,
    use f',
    exact ⟨f'inv, f'cont⟩,
  },
end

lemma bij_inv_bij {X' Y' : Type} (f : X' → Y') (f' : Y' → X') : inverse f f' →
(function.bijective f ↔ function.bijective f') :=
begin
  intros f'inv,
  split;
  intro fbij,
  rw inv_symm at f'inv,
  exact inv_imp_bij f' f f'inv,
  exact inv_imp_bij f f' f'inv,
end

lemma unique_preimage {X' Y' : Type} (f : X' → Y') (f' : Y' → X') : inverse f f' → 
∀ (s : set Y'), preimage f s = image f' s :=
begin
  intros f'inv s,
  have img_img:= left_inverse.image_image f'inv.right s,
  have := inv_imp_bij f f' f'inv,
  rw set.preimage_eq_iff_eq_image this,
  exact eq.symm img_img,
end


-- Finally some solving!!
-- Exercise 2.2.2.
-- cycle implication to show equivalence 
-- (i.e. (h1 → h2 →  ... → hn → h1) ↔ (h1 ↔ h2 ↔ ... ↔ hn) )

lemma step1 (f : X → Y) (fcont : continuous f) : is_homeomorphism f → 
function.bijective f ∧ is_open_map f :=
begin
  intros fhom,
  rcases fhom with ⟨ fbij, fcont, f', f'inv, f'cont ⟩ ,
  refine ⟨ fbij, _ ⟩,
  exact is_open_map.of_inverse f'cont f'inv.right f'inv.left,
end

lemma step2 (f : X → Y) : function.bijective f ∧ is_open_map f → 
function.bijective f ∧ is_closed_map f :=
begin
  intros fhom,
  rcases fhom with ⟨ fbij, fopen ⟩ ,
  refine ⟨ fbij, _ ⟩,

  intros s sclosed,
  have    : is_open sᶜ            := sclosed.is_open_compl,
  have hf : is_open (f '' sᶜ)     := fopen sᶜ this,
  have    : f '' sᶜ = (f '' s)ᶜ   := set.image_compl_eq fbij,
  refine {is_open_compl := _},
  rwa this at hf,
end

lemma step3 (f : X → Y) (fcont : continuous f) : function.bijective f ∧ is_closed_map f →
is_homeomorphism f :=
begin
  intros fclosedbij,
  rw ← hom_homeo_equiv,
  split,
  exact fcont,
  {
    rcases fclosedbij with ⟨ fbij, fclosed ⟩ ,
    rw function.bijective_iff_has_inverse at fbij,
    rcases fbij with ⟨ f', f'inv ⟩ ,
    use f',
    refine ⟨f'inv, _⟩,

    rw continuous_iff_is_closed,
    intros s sclosed,
    have : f' ⁻¹' s = f '' s := unique_preimage f' f ⟨f'inv.right, f'inv.left⟩ s,
    rw this,
    exact fclosed s sclosed,
  },
end

lemma finish_up (f : X → Y) (fcont : continuous f) :
(is_homeomorphism f                      ↔ function.bijective f ∧ is_open_map f    )∧
(function.bijective f ∧ is_open_map f    ↔ function.bijective f ∧ is_closed_map f  )∧
(function.bijective f ∧ is_closed_map f  ↔ is_homeomorphism f                      ):=
begin
  split;
  split,
    exact step1 f fcont,
    intro H,
    exact step3 f fcont (step2 f H),
  split,
    exact step2 f,
    intro H,
    exact step1 f fcont (step3 f fcont H),
  split,
    exact step3 f fcont,
    intro H,
    exact step2 f (step1 f fcont H),
end

/-Exercise 2.2.7. [+] Let 𝒮 be the collection from Exercise 2.2.6. Show that the collection
𝒮𝑛 = {𝑝ᵢ⁻¹(𝑆) ∶ all 𝑆 ∈ 𝒮 and 1 ≤ 𝑖 ≤ 𝑛}
where the 𝑝𝑖 are the 𝑛 coordinate projections, is a subbase for the standard topology on ℝ𝑛
. ♣-/

