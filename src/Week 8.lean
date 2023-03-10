import topology.basic
import topology.maps
import topology.homeomorph
open topological_space
open set filter classical
variables {X Y : Type} [topological_space X] [topological_space Y] [nonempty X] [nonempty Y] {A E F U V : set X}


/-Exercise 2.2.2. [โ] Show that the following are equivalent for a continuous map ๐ โถ ๐ โ ๐
between spaces (๐, ๐ช๐) and (๐, ๐ช๐).
(i) ๐ โถ ๐ โ ๐ is a homeomorphism.
(ii) ๐ is an open bijection.
(iii) ๐ is a closed bijection.
โฃ

Exercise 2.2.7. [+] Let ๐ฎ be the collection from Exercise 2.2.6. Show that the collection
๐ฎ๐ = {๐แตขโปยน(๐) โถ all ๐ โ ๐ฎ and 1 โค ๐ โค ๐}
where the ๐๐ are the ๐ coordinate projections, is a subbase for the standard topology on โ๐
. โฃ-/


-- definitions
-- open function is defined the same way with the name is_open_map
-- the same for closed function
def is_inv {X' Y' : Type} (f : X' โ Y') (f' : Y' โ X') := 
function.left_inverse f f' โง function.right_inverse f f'
def is_homeomorphism (f : X โ Y) := 
function.bijective f โง continuous f โง โ (f' : Y โ X) (H : is_inv f f'), continuous f'
def is_hom (f : X โ Y) := 
continuous f โง โ (f' : Y โ X), is_inv f f' โง continuous f'


-- I am very angry at how inverse function is coded in Lean
-- Are the following lemmas not in lean or am I blind???

lemma inv_imp_bij {X' Y' : Type} (f : X' โ Y') (f' : Y' โ X'):
is_inv f' f โ function.bijective f:=
begin
  intro f'inv,
  refine function.bijective_iff_has_inverse.mpr _,
  use f',
  exact f'inv,
end

lemma linv_imp_rinv_swap {X' Y' : Type} (f : X' โ Y') (f' : Y' โ X') : 
function.left_inverse f f' โ function.right_inverse f' f :=
begin
  intros linv x,
  exact linv x,
end

lemma rinv_imp_linv_swap {X' Y' : Type} (f : X' โ Y') (f' : Y' โ X') : 
function.right_inverse f f' โ function.left_inverse f' f :=
begin
  intros rinv x,
  exact rinv x,
end

lemma inv_swap {X' Y' : Type} (f : X' โ Y') (f' : Y' โ X') : is_inv f f' โ is_inv f' f :=
begin
  intros h,
  split,
  exact rinv_imp_linv_swap f f' h.right,
  exact linv_imp_rinv_swap f f' h.left,
end

lemma inv_symm {X' Y' : Type} (f : X' โ Y') (f' : Y' โ X') : is_inv f f' โ is_inv f' f :=
begin
  split,
  have := inv_swap f f',
  exact this,
  have := inv_swap f' f,
  exact this,
end

lemma hom_homeo_equiv (f : X โ Y) : is_hom f โ is_homeomorphism f :=
begin
  split,
  {
    intros fhom,
    rcases fhom with โจ fcont, f', f'inv, f'cont โฉ ,
    split,
    rw inv_symm at f'inv,
    exact inv_imp_bij f f' f'inv,
    split,
    exact fcont,
    use f',
    exact โจf'inv, f'contโฉ,
  },
  {
    intros fhomeo,
    rcases fhomeo with โจ fbij, fcont, f', f'inv, f'cont โฉ ,
    split,
    exact fcont,
    use f',
    exact โจf'inv, f'contโฉ,
  },
end

lemma bij_inv_bij {X' Y' : Type} (f : X' โ Y') (f' : Y' โ X') : is_inv f f' โ
(function.bijective f โ function.bijective f') :=
begin
  intros f'inv,
  split;
  intro fbij,
  exact inv_imp_bij f' f f'inv,
  exact inv_imp_bij f f' (inv_swap f f' f'inv),
end

lemma unique_preimage {X' Y' : Type} (f : X' โ Y') (f' : Y' โ X') : is_inv f f' โ 
โ (s : set Y'), preimage f s = image f' s :=
begin
  intros f'inv s,
  have img_img:= function.left_inverse.image_image f'inv.left s,
  rw inv_symm at f'inv,
  have := inv_imp_bij f f' f'inv,
  rw set.preimage_eq_iff_eq_image this,
  exact eq.symm img_img,
end


-- Finally some solving!!
-- Exercise 2.2.2.
-- cycle implication to show equivalence 
-- (i.e. (h1 โ h2 โ  ... โ hn โ h1) โ (h1 โ h2 โ ... โ hn) )

lemma step1 (f : X โ Y) (fcont : continuous f) : is_homeomorphism f โ 
function.bijective f โง is_open_map f :=
begin
  intros fhom,
  rcases fhom with โจ fbij, fcont, f', f'inv, f'cont โฉ ,
  split,
  {exact fbij,},
  {exact is_open_map.of_inverse f'cont f'inv.left f'inv.right,},
end

lemma step2 (f : X โ Y) (fcont : continuous f) : function.bijective f โง is_open_map f โ 
function.bijective f โง is_closed_map f :=
begin
  intros fhom,
  rcases fhom with โจ fbij, fopen โฉ ,
  split,
  {exact fbij,},
  {
    intros s sclosed,
    have    : is_open sแถ            := sclosed.is_open_compl,
    have hf : is_open (f '' sแถ)     := fopen sแถ this,
    have    : f '' sแถ = (f '' s)แถ   :=  set.image_compl_eq fbij,
    refine {is_open_compl := _},
    rwa this at hf,
  },
end

lemma step3 (f : X โ Y) (fcont : continuous f) : function.bijective f โง is_closed_map f โ
is_homeomorphism f :=
begin
  intros fclosedbij,
  rw โ hom_homeo_equiv,
  split,
  exact fcont,
  {
    rcases fclosedbij with โจ fbij, fclosed โฉ ,
    rw function.bijective_iff_has_inverse at fbij,
    rcases fbij with โจ f', f'inv โฉ ,
    use f',
    split,
    {exact (inv_symm f' f).mp f'inv,},
    {
      rw continuous_iff_is_closed,
      intros s sclosed,
      have : f' โปยน' s = f '' s := unique_preimage f' f (f'inv) s,
      rw this,
      exact fclosed s sclosed,
    },
  },
end

lemma finish_up (f : X โ Y) (fcont : continuous f) :
(is_homeomorphism f                      โ function.bijective f โง is_open_map f   )โง
(function.bijective f โง is_open_map f   โ function.bijective f โง is_closed_map f )โง
(function.bijective f โง is_closed_map f โ is_homeomorphism f                      ):=
begin
  split;
  split,
    exact step1 f fcont,
    intro H,
    exact step3 f fcont (step2 f fcont H),
  split,
    exact step2 f fcont,
    intro H,
    exact step1 f fcont (step3 f fcont H),
  split,
    exact step3 f fcont,
    intro H,
    exact step2 f fcont (step1 f fcont H),
end

/-Exercise 2.2.7. [+] Let ๐ฎ be the collection from Exercise 2.2.6. Show that the collection
๐ฎ๐ = {๐แตขโปยน(๐) โถ all ๐ โ ๐ฎ and 1 โค ๐ โค ๐}
where the ๐๐ are the ๐ coordinate projections, is a subbase for the standard topology on โ๐
. โฃ-/

