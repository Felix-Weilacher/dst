import .Cantor_Bendixson

variables {α : Type*}

open topological_space
open set

theorem image_Inter' {β γ: Type*} [inhabited γ] {f : α → β} (hf : function.injective f) (s : γ → set α) :
  f '' (⋂ i : γ, s i) = ⋂ i : γ, f '' (s i) :=
begin
  apply subset_antisymm, {
    apply image_Inter_subset,
  },
  intros y hy,
  rw mem_Inter at hy,
  rcases hy default with ⟨x,hx,rfl⟩,
  refine ⟨x,_,rfl⟩,
  rw mem_Inter,
  intro i,
  rcases hy i with ⟨z,hz1,hz2⟩,
  convert hz1,
  symmetry,
  exact hf hz2,
end

instance second_countable_of_polish [topological_space α] [polish_space α] : second_countable_topology α := polish_space.second_countable _

section ctble_gen

variable [s : measurable_space α]
include s

namespace measurable_space

variable (α)

class countable_generated : Prop :=
  (is_generated_countable : ∃ b : set (set α), b.countable ∧ s = generate_from b)


lemma nat_gen [h : countable_generated α] : ∃ f : ℕ → (set α), s = generate_from (range f) :=
begin
  obtain ⟨b,bct,hb⟩ := h.is_generated_countable,
  let c := b ∪ {univ},
  have cct : c.countable, {
    apply countable.union bct,
    apply countable_singleton,
  },
  have cnonempty : c.nonempty, {
    use univ,
    right,
    simp,
  },
  obtain ⟨f,hfc⟩ := (set.countable_iff_exists_surjective cnonempty).mp cct,
  use (λ n, (f n).val),
  rw hb,
  sorry,
end

variable {α}

namespace countable_generated

instance borel_countable_generated_of_second_countable [topological_space α] [borel_space α] [second_countable_topology α] : countable_generated α :=
begin
  constructor,
  have := topological_space.exists_countable_basis α,
  rcases this with ⟨b,bct,bnontrivial,bbasis⟩,
  use [b,bct],
  borelize α,
  apply bbasis.borel_eq_generate_from,
end

open_locale classical
theorem borel_inj_cantor_of_countable_generated_of_singleton_measurable [h : countable_generated α] [measurable_singleton_class α] : ∃ f : α → (ℕ → bool), measurable f ∧ function.injective f :=
begin
  obtain ⟨b,bct,hb⟩ := h.is_generated_countable,
  rw countable_iff_exists_subset_range at bct,
  cases bct with e he,
  let f : α → ℕ → bool := begin
    intros x n,
    exact (x ∈ e n),
  end,
  use f, split, {
    rw measurable_pi_iff,
    intros n,
    apply measurable_to_encodable,
    intros y,
    cases f y n, {
      sorry,
    },
    sorry,
  },
  intros x y hxy,
  --have := @measurable_set_eq _ _ _ y,
  --let p : set α → Prop := λ C, C y → C x,
  have : ∀ B : set α, measurable_set B → (x ∈ B ↔ y ∈ B), {
    intros B,
    rw hb,
    apply generate_from_induction (λ C, x ∈ C ↔ y ∈ C) b, {
      intros t ht,
      obtain ⟨n, rfl⟩ := he ht,
      have : f x n = f y n := by rw hxy,
      dsimp[f] at this,
      simp only [bool.to_bool_eq] at this,
      exact this,
    }, { tauto },
    {
      intros t ht,
      tauto,
    },
    intros t ht,
    rw[mem_Union,mem_Union],
    dsimp at ht,
    split; rintros ⟨n,hn⟩; use n, { rwa ← ht n, }, rwa ht n,
  },
  specialize this _ (@measurable_set_eq _ _ _ y),
  dsimp at this,
  rw this,
end 

end countable_generated
end measurable_space
end ctble_gen

section csb

variables {β : Type*}
variables [measurable_space α] [measurable_space β]

namespace measurable_embedding

open measurable_equiv
open measurable_space

--set_option pp.implicit true
open_locale classical
noncomputable
def subtype_sum_compl {A : set α} (hA : measurable_set A) : A ⊕ (Aᶜ : set α) ≃ᵐ α := 
{ to_fun := sum.elim (λ x, x.val) (λ x, x.val),
  inv_fun := begin
    intros x,
    by_cases x ∈ A, { left, exact ⟨x,h⟩, },
    right, exact ⟨x,h⟩,
  end,
  left_inv := begin
    intros x,
    cases x; simp,
    intros h,
    apply x.property,
    exact h,
  end,
  right_inv := begin
    intros x,
    by_cases x ∈ A; dsimp, {rw dif_pos h, simp,},
    rw dif_neg h, simp,
  end,
  measurable_to_fun := begin
    dsimp,
    apply measurable.sum_elim; apply measurable_subtype_coe,
  end,
  measurable_inv_fun := begin
    dsimp,
    apply measurable.dite; measurability,
  end }

noncomputable
def set_image {f : α → β} (hf : measurable_embedding f) (A : set α) : A ≃ᵐ f '' A :=
begin
  apply measurable_equiv.set.image, {exact hf.injective}, {exact hf.measurable},
  exact hf.measurable_set_image',
end

noncomputable
def schroeder_bernstein {f : α → β} {g : β → α} 
  (hf : measurable_embedding f)(hg : measurable_embedding g) : (measurable_equiv α β) :=
begin
  let F : set α → set α := λ A, (g '' (f '' A)ᶜ)ᶜ,
  suffices : Σ' A : set α, measurable_set A ∧ F A = A, {
    rcases this with ⟨A,Ameas,Afp⟩, --!!
    let B := f '' A,
    have Bmeas : measurable_set B := by {rw hf.measurable_set_image, exact Ameas,},
    apply (subtype_sum_compl Ameas).symm.trans,
    apply measurable_equiv.trans _ (subtype_sum_compl Bmeas),
    apply sum_congr, {
      apply hf.set_image,
    },
    have : Aᶜ = g '' Bᶜ, {
      apply compl_injective,
      rw ← Afp,
      simp,
    },
    rw this,
    apply measurable_equiv.symm,
    apply hg.set_image, 
  },
  have Fmono : ∀ {A B}, A ⊆ B → F A ⊆ F B, {
    intros A B hAB,
    rw compl_subset_compl,
    apply image_subset,
    rw compl_subset_compl,
    apply image_subset,
    assumption,
  },
  let X : ℕ → set α := begin
    intro n,
    induction n with n ih, {
      exact univ,
    },
    exact F ih,
  end,
  use ⋂ n : ℕ, X n, split, {
    apply measurable_set.Inter,
    intros n,
    induction n with n ih, {
      exact measurable_set.univ,
    },
    apply measurable_set.compl,
    apply hg.measurable_set_image',
    apply measurable_set.compl,
    apply hf.measurable_set_image',
    exact ih,
  },
  apply subset_antisymm, {
    apply subset_Inter,
    intros n,
    cases n, {
      apply subset_univ,
    },
    apply Fmono,
    apply Inter_subset,
  },
  rintros x hx ⟨y,hy,rfl⟩,
  rw mem_Inter at hx,
  apply hy,
  rw image_Inter' hf.injective, swap, {apply_instance},
  rw mem_Inter, intro n,
  by_contradiction, --!
  apply (hx n.succ),
  exact ⟨y,h,rfl⟩,
end

end measurable_embedding

noncomputable
def borel_schroeder_bernstein [topological_space α] [polish_space α] [borel_space α]
  [topological_space β] [polish_space β] [borel_space β] {f : α → β} {g : β → α} 
  (fmeas : measurable f) (finj : function.injective f) (gmeas : measurable g) (ginj : function.injective g) :
  α ≃ᵐ β :=
begin
  have hf' := fmeas.measurable_embedding finj,
  have hg' := gmeas.measurable_embedding ginj,
  exact hf'.schroeder_bernstein hg',
end

end csb

