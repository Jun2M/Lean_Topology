import topology.basic
import topology.separation
open topological_space
open set filter classical
variables {X Y : Type} [topological_space X] [topological_space Y]


/- 
I saw Ethan's solution to the exercise 2.4.14 and I very much liked it. 
I wanted to make sure that his solution works so I wrote this code.
If there is a copyright to the solution of a math question, it belongs to Ethan.
-/


-- Exercise 2.4.14. [⋆] Show that if (𝑋, 𝒪) is Hausdorff and 𝑓 ∶ 𝑋 → 𝑋 is continuous, 
-- then the set of fixed points of 𝑓 is closed. 
theorem fixed_points_closed (f : X → X): t2_space X → continuous f → is_closed {x | f x = x }:=
begin
  intros Hausdorff cont,
  apply is_open_compl_iff.mp,
  apply is_open_iff_forall_mem_open.mpr,
  intros x H,
  -- fixed points are closed since its compliment is union of open sets
 
  have H1 : f x ≠ x := H ;                                                                 clear H,
  have H_def := Hausdorff.t2 ;                                                             clear Hausdorff,
  have := H_def x (f x) (ne.symm H1);                                                      clear H_def H1,
  rcases this with ⟨ u, v, u_open, v_open, x_in_u, fx_in_v, u_v_disjoint ⟩ ,
  -- Use Hausdorff to get open sets around x and f x
  
  let U := u ∩ f ⁻¹' v,
  use U,
  -- claim that U is such open set

  refine ⟨_, _, mem_inter x_in_u fx_in_v⟩,
  -- x is obivously in U since x is in both u and f ⁻¹' v (v includes f x)

  {
    clear' u_open v_open x_in_u fx_in_v cont x,
    intros y y_in_U f_y_eq_y,
    -- suppose there is y in U s.t. f y = y

    have y_in_u:          y ∈ u         := mem_of_mem_inter_left y_in_U,
    have y_in_preim_v:    y ∈ f ⁻¹' v   := mem_of_mem_inter_right y_in_U;                  clear y_in_U U,
    have f_y_in_v:      f y ∈ v         := y_in_preim_v;                                   clear y_in_preim_v,
    have y_in_v :         y ∈ v         := mem_of_eq_of_mem (eq.symm f_y_eq_y) f_y_in_v;   clear f_y_in_v f_y_eq_y f,
    -- Contradiction! since u and v are disjoint
    
    have y_set_in_u:    {y} ≤ u         := singleton_subset_iff.mpr y_in_u;                 clear y_in_u,
    have y_set_in_v:    {y} ≤ v         := singleton_subset_iff.mpr y_in_v;                 clear y_in_v,
    have y_set_eq_bot                   := u_v_disjoint y_set_in_u y_set_in_v;              clear y_set_in_u y_set_in_v u_v_disjoint u v,
    have y_in_y_set:     y ∈ {y}        := mem_singleton y,
    exact y_set_eq_bot y_in_y_set,
  },

  -- U is open because u & v both open and f is continuous so f ⁻¹' v also open
  refine (continuous_on_open_iff u_open).mp _ v v_open,
  exact continuous.continuous_on cont,

end
