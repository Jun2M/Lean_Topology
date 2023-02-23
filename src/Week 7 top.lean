import topology.basic
open topological_space
open set filter classical
variables {X : Type} [topological_space X] {A E F U V : set X}

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
