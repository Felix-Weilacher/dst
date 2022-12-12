import topology.metric_space.baire
import measure_theory.constructions.borel_space
import order.filter.curry
import topology.homeomorph

#check @residual

section cfilter

variables {α : Type*}

open set filter

namespace filter

inductive countable_generate_sets (g : set (set α)) : set α → Prop
| basic {s : set α}      : s ∈ g → countable_generate_sets s
| univ                   : countable_generate_sets univ
| superset {s t : set α} : countable_generate_sets s → s ⊆ t → countable_generate_sets t
| Inter {S : set (set α)}  : S.countable → (∀ s ∈ S, countable_generate_sets s) → countable_generate_sets ⋂₀ S

def countable_generate (g : set (set α)) : filter α :=
{ sets := countable_generate_sets g,
  univ_sets := countable_generate_sets.univ,
  sets_of_superset := λ s t, countable_generate_sets.superset,
  inter_sets := λ s t hs ht,
  begin
    let S : set (set α) := {s,t},
    have : s ∩ t = ⋂₀ S := by rw [sInter_insert, sInter_singleton],
    rw this,
    apply countable_generate_sets.Inter S.to_countable,
    rintros u (rfl | hu), --why wont the second hu work as rfl?
    assumption,
    rw mem_singleton_iff at hu,
    rw hu,
    assumption,
  end }

instance countable_generate_countable_Inter_filter {g : set (set α)} : 
  countable_Inter_filter (countable_generate g) :=
begin
  constructor,
  apply countable_generate_sets.Inter,
end

lemma mem_countable_generate_of_mem {g : set (set α)} {s : set α} (h : s ∈ g) : 
  s ∈ countable_generate g := countable_generate_sets.basic h

lemma mem_countable_generate_iff {g : set (set α)} {s : set α} : 
  s ∈ countable_generate g ↔ ∃ S : set (set α), S ⊆ g ∧ S.countable ∧ ⋂₀ S ⊆ s :=
begin
  split, swap,
  { rintros ⟨S,Sg,Sct,Ss⟩, 
    apply mem_of_superset _ Ss,
    apply countable_generate_sets.Inter Sct,
    intros s hs,
    apply mem_countable_generate_of_mem,
    exact Sg hs, },
  intros hs,
  induction hs with s h s t dum st ih T Tct hT ih,
  { exact ⟨{s}, singleton_subset_iff.mpr h, countable_singleton _, by simp⟩ },
  { exact ⟨∅, empty_subset _, countable_empty,subset_univ _⟩, },
  { refine Exists.imp _ ih, 
    rintros S ⟨S1,S2,hS⟩,
    exact ⟨S1,S2,hS.trans st⟩, },
  dsimp at ih,
  choose S Sg Sct hS using ih,
  refine ⟨⋃ (s : set α) (H : s ∈ T), S s H, _, _, _⟩,
  { simp only [Union_subset_iff], exact Sg, },
  { exact countable.bUnion Tct Sct, },
  apply subset_sInter,
  intros s H,
  apply subset_trans _ (hS s H),
  apply sInter_subset_sInter,
  apply subset_Union₂,
end

lemma eventually.eventually_eq {f : filter α} {p q : α → Prop} 
  (hp : ∀ᶠ x in f, p x) (heq : q =ᶠ[f] p) : ∀ᶠ x in f, q x :=
begin
  rw [filter.eventually,← eventually_eq_univ] at *,
  exact heq.trans hp,
end

lemma frequently.eventually_eq {f : filter α} {p q : α → Prop} 
  (hp : ∃ᶠ x in f, p x) (heq : q =ᶠ[f] p) : ∃ᶠ x in f, q x :=
begin
  rw [filter.frequently] at *,
  intros h, 
  apply hp,
  exact h.eventually_eq heq.compl.symm,
end

end filter
end cfilter

section

open set filter

variables (α : Type*) [topological_space α]

def comeager : filter α := filter.countable_generate (λ s, is_open s ∧ dense s)

notation s ` =ᵇ `:50 t := s =ᶠ[comeager _] t
notation s ` ≤ᵇ `:50 t := s ≤ᶠ[comeager _] t
--notation `∀ᵇ `:50 x := ∀ᶠ x in (comeager _) not working
--notation `∃ᵇ `:50 x := ∃ᶠ x in (comeager _)

instance comeager_countable_Inter : countable_Inter_filter (comeager α) := 
begin
  rw[comeager],
  apply_instance,
end

variables {α} 

@[reducible]
def is_comeager (s : set α) : Prop := s ∈ comeager α
def is_meager (s : set α) : Prop := is_comeager sᶜ 

lemma is_comeager_def {s : set α} : s ∈ comeager α ↔ is_comeager s := by refl --rfl doesnt work

lemma is_comeager_iff_eventually_eq_univ {s : set α} : is_comeager s ↔ s =ᵇ univ := 
by rw[eventually_eq_univ]

lemma is_meager_iff_eventually_eq_empty {s : set α} : is_meager s ↔ s =ᵇ (∅ : set α) :=--????
begin
  rw [is_meager,eventually_eq_empty],
  refl,
end

lemma is_comeager_iff_sInter {s : set α} : is_comeager s ↔ 
  ∃ T : set (set α), (∀ t ∈ T, is_open t ∧ dense t) ∧ T.countable ∧ ⋂₀ T ⊆ s :=
begin
  rw [is_comeager,comeager,mem_countable_generate_iff],
  refl,
end

lemma is_meager_iff_sUnion {s : set α} : is_meager s ↔ 
  ∃ T : set (set α), (∀ t ∈ T, is_closed t ∧ interior t = ∅) ∧ T.countable ∧ s ⊆ ⋃₀ T :=
begin
  rw [is_meager,is_comeager_iff_sInter],
  sorry,
end

lemma is_comeager_of_sInter {S : set (set α)} (Sct : S.countable) 
  (hS : ∀ s ∈ S, is_comeager s) : is_comeager ⋂₀ S :=
(countable_sInter_mem Sct).mpr hS

lemma is_meager_of_sUnion {S : set (set α)} (Sct : S.countable) 
  (hS : ∀ s ∈ S, is_meager s) : is_meager ⋃₀ S :=
begin
  rw[is_meager, compl_sUnion],
  apply is_comeager_of_sInter (Sct.image _),
  rintros s ⟨t,tS,rfl⟩,
  apply hS,
  exact tS,
end

lemma is_comeager.eventually_eq {s t : set α} (hs : is_comeager s) (hst : t =ᵇ s) : 
  is_comeager t := eventually.eventually_eq hs hst

lemma is_meager.eventually_eq {s t : set α} (hs : is_meager s) (hst : t =ᵇ s) : 
  is_meager t := is_comeager.eventually_eq hs hst.compl

@[simp]
theorem is_meager_compl_iff {s : set α} : is_meager sᶜ ↔ is_comeager s := 
by rw[is_meager,compl_compl]

@[simp]
theorem is_comeager_compl_iff {s : set α} : is_comeager sᶜ ↔ is_meager s := by refl

lemma is_comeager_of_open_dense {s : set α} (hopen : is_open s)(hdense : dense s) : 
  is_comeager s := filter.mem_countable_generate_of_mem ⟨hopen,hdense⟩

lemma is_closed.sdiff_interior_meager {s : set α} (hs : is_closed s) : 
  is_meager (s \ interior s) :=
begin
  apply is_comeager_of_open_dense,
  { rw is_open_compl_iff,
    exact hs.sdiff is_open_interior, },
  rw [← interior_eq_empty_iff_dense_compl, ← subset_empty_iff],
  have : ∅ = interior s ∩ (s \ interior s), { rw inter_diff_self, },
  rw [this, subset_inter_iff],
  split, { apply interior_mono, apply diff_subset,},
  apply interior_subset,
end

lemma is_open.closure_sdiff_meager {s : set α} (hs : is_open s) : is_meager (closure s \ s) :=
begin
  have := hs.is_closed_compl.sdiff_interior_meager,
  simpa,
end

--def baire_measurable_space (α : Type*) [topological_space α] : Type* := α



variables (α)

def baire_measurable : measurable_space α := 
{ measurable_set' := λ s, ∃ u, is_open u ∧ s =ᵇ u,
  measurable_set_empty := ⟨∅, ⟨is_open_empty, by refl⟩⟩,
  measurable_set_compl := λ s ⟨u,uop,su⟩, by {
    refine ⟨interior uᶜ, is_open_interior, _⟩,
    calc 
    sᶜ =ᵇ uᶜ : su.compl
    ... =ᵇ (uᶜ ∩ interior uᶜ : set α) : by { 
      symmetry,
      rw filter.inter_eventually_eq_left,
      rw [filter.eventually,is_comeager_def, ← is_meager_compl_iff],
      convert uop.is_closed_compl.sdiff_interior_meager,
      ext x,
      simp[and_comm], --this is terrible
     }
    ... = interior uᶜ : by { apply inter_eq_self_of_subset_right, exact interior_subset, }
  },
  measurable_set_Union := λ s hs, by {
    choose u uop hu using hs,
    exact ⟨⋃ i : ℕ, u i, is_open_Union uop, eventually_eq.countable_Union hu⟩,
  }}

variable {α}

def baire_measurable_set (s : set α) : Prop := @measurable_set _ (baire_measurable α) s

lemma borel_le_measurable : borel α ≤ baire_measurable α :=
begin
  apply measurable_space.generate_from_le,
  intros u uop,
  exact ⟨u,uop,by refl⟩,
end

--example (s t : set α) : Prop := s ≤ᶠ[comeager α] t

namespace baire_measurable_set 

open topological_space

theorem localization {s : set α} (hs : baire_measurable_set s) : 
  is_meager s ∨ ∃ u : set α, is_open u ∧ u.nonempty ∧ s =ᵇ u :=
begin
  rcases hs with ⟨u,uop,hu⟩,
  cases eq_empty_or_nonempty u with h h,
  { left, rwa [is_meager_iff_eventually_eq_empty, ←h], },
  right, exact ⟨u,uop,h,hu⟩,
end

theorem basis_localization {s : set α} (hs : baire_measurable_set s)  {b : set (set α)} 
  (hb : is_topological_basis b) : is_meager s ∨ ∃ u ∈ b, u ≤ᵇ s :=
begin
  cases hs.localization with h h, 
  {left, exact h},
  right,
  rcases h with ⟨v,vop,vnon,hv⟩,
  rcases hb.exists_nonempty_subset vnon vop with ⟨u,ub,-,uv⟩,
  use [u,ub],
  calc
  u ≤ᵇ v : uv.eventually_le
  ... =ᵇ s : hv.symm
end

end baire_measurable_set


section homeomorphism

#check homeomorph
variables {β : Type*} [topological_space β] (f : α ≃ₜ β)

#check filter.map f

theorem map_comeager_eq_comeager : filter.map f (comeager α) = comeager β :=
begin
  sorry,
end


end homeomorphism

section KU 

open topological_space function

variables {β : Type*} [topological_space β]
variables {A : set (α × β)}

lemma curry_eq {α β γ : Type*} (f : α × β → γ) (x : α) (y : β) : 
  f (x,y) = f.curry x y := by simp[function.curry]

instance countable_Inter_filter_curry {α β: Type*} {f : filter α} {g : filter β} 
  [countable_Inter_filter f] [countable_Inter_filter g] : countable_Inter_filter (f.curry g) :=
begin
  constructor,
  intros S Sct hS,
  dsimp[filter.curry],
  simp_rw[eventually_countable_ball Sct],
  exact hS,
end

lemma filter.frequently_curry_iff {α β: Type*} {f : filter α} {g : filter β} {p : α × β → Prop} :
  (∃ᶠ z in f.curry g, p z) ↔ (∃ᶠ x in f, ∃ᶠ y in g, p (x,y)) := 
by simp only[filter.frequently, eventually_curry_iff, not_not]

lemma is_open.section (h : is_open A) (x : α) : is_open (A.curry x) :=
begin
  refine continuous_def.mp _ A h,
  exact continuous.prod.mk x,
end

#check is_open.section
#check λ x, A.curry x
#check λ y, λ x, A.curry x y

--set_option pp.all true
theorem curry_le_comeager [second_countable_topology β] : 
  (comeager α).curry (comeager β) ≤ comeager (α × β) :=
begin
  intros A hA,
  rw [is_comeager_def,is_comeager_iff_sInter] at hA,
  rcases hA with ⟨T,hT,Tct,TA⟩,
  apply mem_of_superset _ TA,
  rw countable_sInter_mem Tct, swap, { apply_instance }, --why didn't this instance get found?
  intros t ht,
  obtain ⟨top,tdense⟩ := hT _ ht,
  apply eventually_curry_iff.mpr,
  simp_rw [curry_eq t],
  have : ∀ x : α, dense (t.curry x) → is_comeager (t.curry x) := λ x h, is_comeager_of_open_dense (top.section x) h,
  apply eventually.mono _ this,
  --apply eventually.mono _ (λ x : α, is_comeager_of_open_dense (topen.section x)),
  obtain ⟨b,bct,-,bbasis⟩ := exists_countable_basis β,
  simp_rw [bbasis.dense_iff, eventually_countable_ball bct],
  intros u ub,
  have uop := bbasis.is_open ub,
  rw eventually_imp_distrib_left,
  intro hu,
  have : {x : α | (u ∩ curry t x).nonempty} = (prod.fst) '' ((univ ×ˢ u) ∩ t),
  { simp only [set.nonempty, image, function.curry, mem_inter_iff, 
      mem_prod, mem_univ, true_and, prod.exists,
    exists_and_distrib_right, exists_eq_right], refl, },
  apply is_comeager_of_open_dense; rw this,
  { apply is_open_map_fst, 
    exact (is_open_univ.prod uop).inter top, },
  rw dense_iff_inter_open at *,
  intros v vop hv,
  rcases tdense _ (vop.prod uop) (hv.prod hu) with ⟨⟨x,y⟩,⟨xv,yu⟩,xyt⟩,
  refine ⟨x,xv,_⟩,
  simp only [mem_image, mem_inter_iff, mem_prod, mem_univ, true_and, prod.exists, exists_and_distrib_right, exists_eq_right],
  exact ⟨y,yu,xyt⟩,
end

lemma topological_space.is_topological_basis.is_open_Union_countable_basis 
  [second_countable_topology α] {b : set (set α)} (hb : is_topological_basis b) 
  {U : set α} (hU : is_open U) : ∃ t : set (set α), t.countable ∧ t ⊆ b ∧ ⋃₀ t = U :=
begin
  rw hb.open_iff_eq_sUnion at hU,
  rcases hU with ⟨S,hS,rfl⟩,
  apply exists_imp_exists _ (is_open_sUnion_countable S _), { tauto },
  refine hS.trans _,
  intro u, 
  exact hb.is_open,
end

lemma is_meager.prod_left {u : set α} {v : set β} (hu : is_meager u) : is_meager (u ×ˢ v) :=
begin
  rw [is_meager, is_comeager_iff_sInter] at *,
  rcases hu with ⟨T, hT, Tct, Tu⟩,
  use (λ t : set α, t ×ˢ univ) '' T,
  refine ⟨_, by apply Tct.image, _⟩,
  { rintros s ⟨t,tT,rfl⟩,
    specialize hT t tT,
    split, { exact hT.1.prod is_open_univ, },
    exact hT.2.prod dense_univ,},
  intros p,
  simp only [sInter_image, mem_Inter, mem_prod, mem_univ, and_true, mem_compl_iff, not_and],
  intros pT pu,
  exfalso,
  exact Tu pT pu,
end

lemma is_meager.prod_right {u : set α} {v : set β} (hv : is_meager v) : is_meager (u ×ˢ v) :=
begin
  rw [is_meager, ← is_comeager_def, ← map_comeager_eq_comeager (homeomorph.prod_comm _ _), 
    homeomorph.coe_prod_comm, mem_map, preimage_compl, preimage_swap_prod, 
    is_comeager_def, is_comeager_compl_iff],
  apply hv.prod_left,
end

theorem eventually_eventually_of_comeager [second_countable_topology β] (hA : is_comeager A) : 
  ∀ᶠ x in (comeager α), ∀ᶠ y in (comeager β), (x,y) ∈ A := curry_le_comeager hA

theorem frequently_frequently_of_not_meager [second_countable_topology α]      
  [second_countable_topology β] 
  (hmeas : baire_measurable_set A) (hA : ¬ is_meager A) : 
  ∃ᶠ x in (comeager α), ∃ᶠ y in (comeager β), (x,y) ∈ A :=
begin
  rcases hmeas with ⟨U,Uop,hU⟩,
  rcases ((@is_topological_basis_opens α _).prod 
    (@is_topological_basis_opens β _)).is_open_Union_countable_basis Uop with ⟨T, Tct, Trect, rfl⟩,
  obtain ⟨t, tT, ht⟩ : ∃ t, t ∈ T ∧ ¬ is_meager t,
  { contrapose! hA,
    apply is_meager.eventually_eq _ hU,
    exact is_meager_of_sUnion Tct hA, },
  rcases Trect tT with ⟨u, v, -, -, rfl⟩, 
  have hu : ¬ is_meager u := λ h, ht h.prod_left,
  have hv : ¬ is_meager v := λ h, ht h.prod_right,
  apply (@filter.frequently_curry_iff _ _ _ _ A).mp,
  apply frequently.eventually_eq _ (curry_le_comeager hU),
  apply frequently.mono _ (subset_sUnion_of_mem tT),
  simp only [filter.frequently_curry_iff, mem_prod, 
    frequently_and_distrib_left, frequently_and_distrib_right],
  exact ⟨hu, hv⟩,
end

theorem baire_measurable_sections_left [second_countable_topology β] 
  (hA : baire_measurable_set A) : ∀ᶠ x in (comeager α), baire_measurable_set (A.curry x) :=
begin
  rcases hA with ⟨U,Uop,hU⟩,
  apply eventually.mono (eventually_eventually_of_comeager hU),
  intros x hx,
  refine ⟨U.curry x,_,hx⟩,
  apply Uop.section,
end

theorem baire_measurable_sections_right [second_countable_topology α] :
  ∀ᶠ y in (comeager β), baire_measurable_set (λ x, A.curry x y) :=
begin
  sorry,
end

lemma curry_eq_comeager [second_countable_topology α] [second_countable_topology β] 
  (hmeas : baire_measurable_set A) : 
  is_comeager A ↔ ∀ᶠ x in (comeager α), ∀ᶠ y in (comeager β), (x,y) ∈ A :=
begin
  split, { apply curry_le_comeager, },
  contrapose, 
  intro hA,
  simp only [not_eventually, ← mem_compl_iff],
  apply frequently_frequently_of_not_meager hmeas.compl,
  simp[hA],
end

/-
theorem curry_eq_comeager [second_countable_topology α] [second_countable_topology β] 
  (hmeas : baire_measurable_set A) : 
  is_comeager A ↔ ∀ᶠ x in (comeager α), ∀ᶠ y in (comeager β), (x,y) ∈ A :=
begin
  split, { apply curry_le_comeager },
  intro hA,
  rcases hmeas.compl with ⟨U,Uop,hU⟩,
  rcases ((@is_topological_basis_opens α _).prod 
    (@is_topological_basis_opens β _)).is_open_Union_countable_basis Uop with ⟨T, Tct, Trect, rfl⟩,
  have : ∀ t ∈ T, is_meager t,
  { intros t ht,
    rcases Trect ht with ⟨u, v, uop, vop, rfl⟩, 
    suffices : (is_meager u) ∨ (is_meager v),
    { cases this with hu hv, 
      { exact hu.prod_left, },
      exact hv.prod_right, },
    by_contra',
    let f := (comeager α).curry (comeager β),
    have h1 : A ∈ f := hA,
    have h2 : (⋃₀ T)ᶜ ∈ f,
    { rw ← eventually_eq_univ at *,
      calc
      (⋃₀ T)ᶜ =ᶠ[f] Aᶜᶜ : curry_le_comeager (hU.compl.symm)
      ... = A : by rw compl_compl
      ... =ᶠ[f] univ : h1 },
    have h3 : (u ×ˢ v)ᶜ ∈ f,
    { apply filter.mem_of_superset h2,
      rw [compl_subset_compl],
      exact subset_sUnion_of_mem ht,  },
    have h4 : ∃ᶠ x in (comeager α), ∃ᶠ y in (comeager β), (x,y) ∈ (u ×ˢ v),
    { simp only [prod_mk_mem_set_prod_eq, frequently_and_distrib_left, frequently_and_distrib_right], 
      exact this, },
    have h5 : ∃ᶠ p in f, p ∈ (u ×ˢ v),
    { rw[filter.frequently, eventually_curry_iff],
      simp_rw [not_eventually,not_not],
      exact h4, },
    contradiction, },
  rw [is_comeager_iff_eventually_eq_univ],
  calc
  A = Aᶜᶜ : by rw compl_compl
  ... =ᵇ (⋃₀ T)ᶜ : hU.compl
  ... =ᵇ univ : by 
  { rw [compl_sUnion, eventually_eq_univ, countable_sInter_mem],
    { rintros - ⟨t,tT,rfl⟩, apply this, exact tT, },
    apply Tct.image, },
end
-/

end KU

end