import .Borel_Isomorphism

class standard_borel (α : Type*) [measurable_space α] : Prop :=
  (is_polishable : ∃ τ : topological_space α, polish_space α ∧ borel_space α)

class upgraded_standard_borel (α : Type*) extends measurable_space α, 
  topological_space α, borel_space α, polish_space α

noncomputable
def upgrade_standard_borel (α : Type*) [hm : measurable_space α] [hs : standard_borel α] :
  upgraded_standard_borel α :=
begin
  choose τ hp hb using hs.is_polishable,
  letI := τ,
  apply upgraded_standard_borel.mk,
end

section clopenable

open measurable_space
variables {α : Type*}

set_option pp.implicit true
theorem eq_borel_of_polish_le_polish {s t : topological_space α} 
  (hs : @polish_space _ s) (ht : @polish_space _ t) (h : s ≤ t) : @borel _ s = @borel _ t :=
begin
  dsimp[borel],
  apply le_antisymm; apply generate_from_le; intros X hX,  {
    have := @is_open.is_clopenable _ s _ X hX,
    rcases this with ⟨r,rs,hr⟩,
    rw ← @measure_theory.is_clopenable_iff_measurable_set _ t _ (@borel _ t) (by {
      exact @borel_space.mk α t (@borel α t) (@rfl (measurable_space α) (@borel α t)),
    }),
    refine ⟨r,_,hr⟩,
    exact le_trans rs h,
  },
  apply measurable_set_generate_from,
  apply h,
  exact hX,
end

lemma clopenable_same_borel [t : topological_space α] [ht : polish_space α] 
  [m : measurable_space α] [hb : borel_space α]
  {X : set α} (hX : polish_space.is_clopenable X) : ∃ s : topological_space α,
  (@polish_space _ s) ∧ @is_closed _ s X ∧ @is_open _ s X ∧ @borel_space _ s _ :=
begin
  rcases hX with  ⟨s,st,hs1,hs2,hs3⟩,
  refine ⟨s,hs1,hs2,hs3,_⟩,
  constructor,
  rw hb.measurable_eq,
  symmetry,
  apply eq_borel_of_polish_le_polish; assumption,
end

end clopenable

section sb_instances

variables {α β: Type*} 
variables [measurable_space α] [standard_borel α] [measurable_space β] [standard_borel β]

--set_option pp.implicit true
theorem measurable_set.standard_borel {s : set α} (hs : measurable_set s) : standard_borel s :=
begin
  letI := upgrade_standard_borel α,
  rw ← measure_theory.is_clopenable_iff_measurable_set at hs,
  rcases clopenable_same_borel hs with ⟨t,tpolish,sclosed,-,ht⟩,
  letI := t,
  constructor,
  use infer_instance,
  split, {
    apply sclosed.polish_space,
  },
  apply_instance,
end 

instance prod_standard_borel : standard_borel (α × β) :=
begin
  letI := upgrade_standard_borel α,
  letI := upgrade_standard_borel β,
  constructor,
  use[infer_instance],
  sorry, --no polish_space.prod!
end



end sb_instances
