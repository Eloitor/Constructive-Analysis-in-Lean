import data.rat
import data.analysis.topology
import data.set.basic
import init.algebra.classes
import regular_sequence
import order.filter.basic

open set
universe u

variables {T: Type u}[lattice T][is_total T has_le.le]

def left_ray : T → (set T) := λ a, {x : T | x ≤ a}

lemma left_ray_inter(a b: T): left_ray a ∩ left_ray b = left_ray (a ⊓ b) :=
  set.ext (λ x, ⟨(λ h, by rwa [left_ray,mem_set_of_eq, le_inf_iff]), 
    (λ h, by rwa [left_ray, mem_inter_eq, mem_set_of_eq, mem_set_of_eq, ← le_inf_iff])⟩)

def left_ray_topology : topological_space ℤ :=
{ is_open := λ U, U = ∅ ∨ U = univ ∨ ∃ z, U = left_ray z,
  is_open_univ := by tauto,
  is_open_inter := 
  begin
    intros U V hU hV,
    rcases hU,
    {
      left,
      rw hU,
      simp,
    },
    {
      cases hU,
      {
        cases hV,
        {
          left,
          rw hV,
          simp,
        },
        {
          cases hV,
          {
            right,
            left,
            rw [hV, hU],
            simp,
          },
          {
            right,
            right,
            rw hU,
            simpa,
          },
        },
      },
      {
        cases hV,
        {
          left,
          rw hV,
          simp,
        },
        {
          cases hV,
          {
            right,
            right,
            rw hV,
            simpa,
          },
          {
            right,
            right,
            obtain ⟨z1, hz1⟩ := hU,
            obtain ⟨z2, hz2⟩ := hV,
            use z1 ⊓ z2,
            rw [hz1, hz2],
            exact left_ray_inter z1 z2,
          },
          },
        },
      },
  end,
  is_open_sUnion := sorry }
