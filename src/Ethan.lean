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


-- Exercise 2.4.14. [โ] Show that if (๐, ๐ช) is Hausdorff and ๐ โถ ๐ โ ๐ is continuous, 
-- then the set of fixed points of ๐ is closed. 
theorem fixed_points_closed (f : X โ X): t2_space X โ continuous f โ is_closed {x | f x = x }:=
begin
  intros Hausdorff cont,
  apply is_open_compl_iff.mp,
  apply is_open_iff_forall_mem_open.mpr,
  intros x H,
  -- fixed points are closed since its compliment is union of open sets
 
  have H1 : f x โ  x := H ;                                                                 clear H,
  have H_def := Hausdorff.t2 ;                                                             clear Hausdorff,
  have := H_def x (f x) (ne.symm H1);                                                      clear H_def H1,
  rcases this with โจ u, v, u_open, v_open, x_in_u, fx_in_v, u_v_disjoint โฉ ,
  -- Use Hausdorff to get open sets around x and f x
  
  let U := u โฉ f โปยน' v,
  use U,
  -- claim that U is such open set

  refine โจ_, _, mem_inter x_in_u fx_in_vโฉ,
  -- x is obivously in U since x is in both u and f โปยน' v (v includes f x)

  {
    clear' u_open v_open x_in_u fx_in_v cont x,
    intros y y_in_U f_y_eq_y,
    -- suppose there is y in U s.t. f y = y

    have y_in_u:          y โ u         := mem_of_mem_inter_left y_in_U,
    have y_in_preim_v:    y โ f โปยน' v   := mem_of_mem_inter_right y_in_U;                  clear y_in_U U,
    have f_y_in_v:      f y โ v         := y_in_preim_v;                                   clear y_in_preim_v,
    have y_in_v :         y โ v         := mem_of_eq_of_mem (eq.symm f_y_eq_y) f_y_in_v;   clear f_y_in_v f_y_eq_y f,
    -- Contradiction! since u and v are disjoint
    
    have y_set_in_u:    {y} โค u         := singleton_subset_iff.mpr y_in_u;                 clear y_in_u,
    have y_set_in_v:    {y} โค v         := singleton_subset_iff.mpr y_in_v;                 clear y_in_v,
    have y_set_eq_bot                   := u_v_disjoint y_set_in_u y_set_in_v;              clear y_set_in_u y_set_in_v u_v_disjoint u v,
    have y_in_y_set:     y โ {y}        := mem_singleton y,
    exact y_set_eq_bot y_in_y_set,
  },

  -- U is open because u & v both open and f is continuous so f โปยน' v also open
  refine (continuous_on_open_iff u_open).mp _ v v_open,
  exact continuous.continuous_on cont,

end
