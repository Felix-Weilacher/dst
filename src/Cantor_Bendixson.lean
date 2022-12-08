/- Author : Felix Weilacher -/
import measure_theory.constructions.polish

--Reference for everything in this file: Chapter 6 of Kechris

open topological_space
open set

section res 

open list

parameter {α : Type*}

-- returns the first n entries of x as a list, but in reverse order.
-- this order works more naturally with the topology on ℕ → α 
def res (x : ℕ → α) : ℕ → list α
  | 0 := nil 
  | (nat.succ n) := (x n) :: res n

@[simp] theorem res_zero (x : ℕ → α) : res x 0 = @nil α := rfl
@[simp] theorem res_succ (x : ℕ → α) (n : ℕ) : res x n.succ = (x n) :: (res x n) := rfl 

@[simp] theorem res_length (x : ℕ → α) (n : ℕ) : (res x n).length = n :=
begin
  induction n with n ih, 
  { refl, },
  simp[ih],
end

-- The restrictions of x and y to n are equal if and only if their first n entries are equal
theorem res_eq_iff (x y : ℕ → α) (n : ℕ) : res x n = res y n ↔ ∀ m < n, x m = y m :=
begin
  split; intro h; induction n with n ih, { simp, }, 
  { intros m hm,
    rw nat.lt_succ_iff_lt_or_eq at hm,
    simp only [res_succ] at h,
    cases hm with hm hm, 
    { apply ih h.2, assumption},
    rw hm,
    exact h.1, },
  { simp },
  { simp only [res_succ],
    split, 
    { apply h,
      apply nat.lt_succ_self, },
    apply ih,
    intros m hm,
    apply h,
    apply nat.lt_succ_of_lt hm, }
end

-- Two infniite sequences are equal if and only if all their restrictions are.
theorem eq_iff_res_eq (x y : ℕ → α) : (∀ n, res x n = res y n) ↔ x = y :=
begin
  split; intro h, 
  { ext n,
    specialize h n.succ,
    rw res_eq_iff at h,
    apply h,
    apply nat.lt_succ_self, },
  rw h,
  simp,
end

--relates res to the basic clopen sets pi_nat.cylinder
theorem cylinder_eq (x : ℕ → α) (n : ℕ) : pi_nat.cylinder x n = {y | res y n = res x n} :=
begin
  ext y, dsimp[pi_nat.cylinder], 
  rw res_eq_iff,
end


theorem cylinder_open [topological_space α] [discrete_topology α] (x : ℕ → α) (n : ℕ) : 
  is_open (pi_nat.cylinder x n) :=
begin
  --copy pasted from library
  rw pi_nat.cylinder_eq_pi,
  exact is_open_set_pi (finset.range n).finite_to_set (λ a ha, is_open_discrete _),
end

end res

section set_seq

open metric
open filter

/- The proof of Cantor-Bendixson we follow makes use a sequence of sets with the same order 
(w.r.t. reverse inclusion) structure as 2^{<ω}. 
This sort of thing is sometimes called a scheme.
Before definining schemes, we establish some basic definitions and theorems 
for sequences of sets with order type ω-/ 
parameters {α : Type*} (A : ℕ → set α)

--The diameter of our sets goes to 0 as n → ∞
def seq_vanishing_diam [pseudo_metric_space α]: Prop := ∀ ε > 0, 
  (∀ᶠ (n : ℕ) in at_top, bounded (A n) ∧ diam (A n) < ε)

--Our sequence is monotone w.r.t. ⊇ 
def seq_mono : Prop := ∀ n : ℕ, (A n.succ) ⊆ A n

--Our definition of monotone in terms of the successor matches the more natural one
theorem seq_mono_iff : seq_mono ↔ ∀ n m : ℕ, m ≥ n → A m ⊆ A n :=
begin
  split; intro h, 
  { intros n m hnm,
    obtain ⟨k, rfl : m = n + k⟩ := le_iff_exists_add.mp hnm,
    clear hnm,
    induction k with k ih, 
    { refl, },
    apply subset_trans _ ih,
      rw [nat.add_succ],
      apply subset_trans _ (h _),
      refl, },
  intros n,
  apply h n n.succ,
  exact nat.le_succ n,
end

--some basic unpacking of seq_vanishing_diam
theorem small_dist_of_vanishing_diam [pseudo_metric_space α]: 
  seq_vanishing_diam → ∀ ε > 0, ∃ n : ℕ, ∀ x y ∈ (A n), dist x y < ε :=
begin
  intros H ε ε_pos,
  specialize H ε ε_pos,
  rw eventually_at_top at H,
  rcases H with ⟨N,hN⟩,
  use N,
  intros x hx y hy,
  specialize hN N (le_refl _),
  apply lt_of_le_of_lt _ hN.2,
  apply dist_le_diam_of_mem hN.1; assumption,
end

--the above theorem is an equivalence
theorem mono_vanishing_diam_iff [pseudo_metric_space α] (hmono : seq_mono) : 
  seq_vanishing_diam ↔ ∀ ε > 0, ∃ n : ℕ, ∀ x y ∈ (A n), dist x y < ε :=
begin
  split, { exact small_dist_of_vanishing_diam, },
  intros h ε ε_pos,
  cases h (ε / 2) (by linarith) with N hN,
  rw eventually_at_top,
  use N,
  intros n hn,
  have : ∀ (x : α), x ∈ A n → ∀ (y : α), y ∈ A n → dist x y ≤ ε / 2, 
  { intros x hx y hy,
    apply le_of_lt,
    rw seq_mono_iff at hmono,
    apply hN; apply hmono _ _ hn; assumption, },
  use ε / 2, {exact this},
  calc 
  diam (A n) ≤ ε / 2 : by 
  { apply diam_le_of_forall_dist_le, {linarith},
    exact this, }
  ... < ε : by linarith
end

--this strengthens monotonicity by requiring the closures of later sets to be contained in previous ones
def seq_closure_mono [topological_space α]: Prop := ∀ n : ℕ, closure (A n.succ) ⊆ A n 

theorem seq_mono_of_seq_closure_mono [topological_space α] : seq_closure_mono → seq_mono :=
begin
  intros h n,
  apply subset_trans _ (h _),
  apply subset_closure,
end

--The intersection of a sequence with vanishing diameter and the 
--"closure_mono" condition is a singleton if the space is complete.
theorem exists_unique_of_closure_mono_of_vanishing_diam [metric_space α] [complete_space α] 
  (hnonempty : ∀ n, (A n).nonempty) (hmono : seq_closure_mono) (hdiam : seq_vanishing_diam) :  
  exists_unique (λ x : α, ∀ n, x ∈ A n) :=
begin
  have Amono : ∀ n : ℕ, ∀ m ≥ n, A m ⊆ A n, 
  { rw ← seq_mono_iff,
    exact seq_mono_of_seq_closure_mono hmono, },
  have hdist := small_dist_of_vanishing_diam hdiam,
  choose u hu using hnonempty,
  have : cauchy_seq u, 
  { rw metric.cauchy_seq_iff',
    intros ε ε_pos,
    cases hdist ε ε_pos with N hN,
    use N,
    intros n hn,
    apply hN, { apply Amono _ _ hn, apply hu, },
    apply hu, },
  cases cauchy_seq_tendsto_of_complete this with x hx,
  have : ∀ n, x ∈ A n, 
  { intros n,
    apply hmono,
    apply (is_closed_closure).mem_of_tendsto hx,
    rw eventually_at_top,
    use n.succ,
    intros m hm,
    apply subset_closure,
    apply Amono _ _ hm,
    apply hu, },
  use [x,this],
  dsimp,
  intros y hy,
  apply eq_of_forall_dist_le,
  intros ε ε_pos,
  cases hdist ε ε_pos with n hn,
  apply le_of_lt,
  rw dist_comm,
  apply hn, {apply this,}, apply hy,
end

end set_seq

--The aforementinoed notion of a scheme
def scheme (β α : Type*) := list β → set α

namespace scheme

open metric
open filter

variables {β α : Type*} (A : scheme β α)

def nonempty : Prop := ∀ s, (A s).nonempty

def branch (x : ℕ → β) : ℕ → set α := λ n, A (res x n)

def vanishing_diam [pseudo_metric_space α] : Prop := 
  ∀ x : (ℕ → β), seq_vanishing_diam (A.branch x)

--A typical way to establish that diameter is vanishing along all branches of a scheme 
--is to know that it vanishes uniformly along each one.
theorem  vanishing_diam_of_vanishing_with_length [pseudo_metric_space α] 
  (u : ℕ → ℝ) (hu : tendsto u at_top (nhds 0))
  (h : ∀ s : list β, ∀ b : β, bounded (A (b :: s)) ∧ diam (A (b :: s)) < u s.length) :
  A.vanishing_diam :=
begin
  intros x ε ε_pos,
  rw eventually_at_top,
  rw at_top_basis.tendsto_iff metric.nhds_basis_ball at hu,
  swap, {apply_instance},
  cases hu ε ε_pos with N hN,
  simp at hN,
  use N.succ, intros m hm,
  dsimp[branch],
  obtain ⟨m, rfl⟩ : ∃ n : ℕ, m = n.succ, 
  { apply nat.exists_eq_succ_of_ne_zero,
    apply ne_of_gt,
    apply lt_of_lt_of_le _ hm,
    apply nat.succ_pos, },
  simp,
  split, {exact (h _ _).1},
  apply (h _ _).2.trans,
  simp,
  apply lt_of_abs_lt,
  apply hN,
  exact nat.le_of_succ_le_succ hm,
end

def disjoint : Prop := ∀ s : list β, ∀ {a b : β}, a ≠ b → disjoint (A (a :: s)) (A (b :: s))

def closure_mono [topological_space α] : Prop := ∀ s : list β, ∀ a : β, 
  closure (A (a :: s)) ⊆ A s

--The scheme version of closure_mono yields the sequence version along each branch
theorem seq_closure_mono_branch_of_closure_mono [topological_space α] (h: closure_mono A) : 
  ∀ x : ℕ → β, seq_closure_mono (A.branch x) :=
begin
  intros x n,
  simp[branch],
  apply h,
end

section map

/-The main purpose of a scheme list β → set α is to build a limiting map (ℕ → β) → α 
This section proves an existence theorem for such maps,
and relates their properties to properties of the scheme. 
Much will have to be added here, and probably the definition of a scheme_map generalized, 
in order to carry out scheme-style proofs beyond Cantor-Bendixson, 
but I think this section should be a good start.
-/
structure scheme_map {β α : Type*} (A : scheme β α) :=
  (map : (ℕ → β) → α)
  (mem : ∀ x : ℕ → β, ∀ n : ℕ, map x ∈ (A.branch x n))

--A scheme map exists if the scheme has nonempty sets, has vanishing diameter along each branch, 
--and has the closure_mono condition
noncomputable
def map_from_closed_mono_and_vanishing_diam [metric_space α] [complete_space α] 
  (hnonempty : A.nonempty) (hmono : A.closure_mono) (hdiam : A.vanishing_diam) : A.scheme_map :=
begin
  have := λ x, exists_unique_of_closure_mono_of_vanishing_diam (A.branch x) _ _ _,
  swap, 
  { dsimp[branch],
    dsimp[nonempty] at hnonempty,
    intro n,
    apply hnonempty, }, swap, 
  { apply seq_closure_mono_branch_of_closure_mono,
    assumption, }, swap, 
  { apply hdiam, },
  choose f hf using this,
  constructor, swap, 
  { exact f, },
  intros x,
  exact (hf _).1,
end

open function

--A scheme map is injective if the children of a given node are always pairwise disjoint
theorem map_inj_of_disjoint (f : scheme_map A) (hdisj : A.disjoint) : injective f.map :=
begin
  intros x y hxy,
  rw ← eq_iff_res_eq,
  intro n,
  induction n with n ih; simp,
  split, 
  { have hx := f.mem x n.succ,
    have hy := f.mem y n.succ,
    dsimp [branch] at hx,
    dsimp [branch] at hy,
    rw [hxy,ih] at hx,
    by_contradiction,
    have := hdisj (res y n) h,
    rw set.disjoint_iff at this,
    apply this, swap, {exact f.map y},
    simp[hy,hx], },
  exact ih,
end

--to avoid conflict with metric.eventually_nhds_iff. Not sure if there is a better way 
--to accomplish this
/- @[protected] lemma eventually_nhds_iff' {α : Type*} [topological_space α] {a : α} {p : α → Prop} : 
  (∀ᶠ (x : α) in nhds a, p x) ↔ ∃ (t : set α), (∀ (x : α), x ∈ t → p x) ∧ is_open t ∧ a ∈ t :=
  eventually_nhds_iff -/

--A scheme map is continuous if diameter vanishes along each branch
theorem map_cts_of_vanishing_diam [pseudo_metric_space α] [topological_space β] 
  [discrete_topology β] (f:scheme_map A) (hdiam : A.vanishing_diam) : 
  continuous f.map :=
begin
  rw continuous_iff',
  intros x ε ε_pos,
  have := small_dist_of_vanishing_diam _ (hdiam x),
  cases this ε ε_pos with n hn,
  rw _root_.eventually_nhds_iff,
  use pi_nat.cylinder x n,
  split, 
  { intros y hy,
    apply hn, 
    { dsimp[branch],
      rw cylinder_eq at hy,
      dsimp at hy,
      rw ← hy,
      apply f.mem, },
    apply f.mem, }, split, 
  { apply cylinder_open, },
  exact pi_nat.self_mem_cylinder x n,
end

end map

end scheme

variables {α : Type*}

/- A set in a topological space is called perfect if it is closed and has no isolated points
Some authors exclude the empty set from being counted as perfect.
This is often useful, and is a separate definition: perf_nonempty -/
def perfect [topological_space α ] (C : set α) : Prop := 
  is_closed C ∧ ∀ x ∈ C, ∀ U ∈ nhds x, ∃ y ∈ U ∩ C, y ≠ x

namespace perfect

variable [topological_space α]

-- The closure of the intersection of a perfect set and an open set is perfect
theorem perfect_of_open_inter {C : set α} (hC : perfect C) (U : set α) (hU : is_open U) : 
  perfect (closure (U ∩ C)) :=
begin
  split, { 
    exact is_closed_closure, },
  intros x hx V hV,
  have : x ∈ C, 
  { rw ← hC.1.closure_eq,
    apply closure_mono _ hx,
    apply inter_subset_right, },
  rw mem_closure_iff_nhds at hx,
  specialize hx V hV,
  cases hx with z hz,
  by_cases z = x, 
  { rw h at hz,
    have := hC.2 x hz.2.2 (V ∩ U) _, 
    { rcases this with ⟨y,hy,ynex⟩,
      use y,
      split, 
      { use hy.1.1,
        apply subset_closure,
        exact ⟨hy.1.2,hy.2⟩, },
    assumption, },
    apply filter.inter_mem hV,
    rw mem_nhds_iff,
    use[U,by refl, hU, hz.2.1], },
  use [z,hz.1],
  apply subset_closure,
  exact hz.2,
end

end perfect

def perf_nonempty [topological_space α] (C : set α) : Prop := set.nonempty C ∧ perfect C

namespace perf_nonempty

-- The closure of the intersection of a nonempty perfect set and an open set is nonempty perfect, 
-- provided the open set is a neighborhood of some point in the perfect set
theorem perf_nonempty_of_open_nhd_inter [topological_space α] {C : set α} 
  (hC : perf_nonempty C) (x : α) (xC : x ∈ C) (U : set α) (xU : x ∈ U) (Uop : is_open U) : perf_nonempty (closure (U ∩ C)) :=
begin
  split, 
  { use x,
    apply subset_closure,
    exact ⟨xU,xC⟩, },
  apply hC.2.perfect_of_open_inter,
  assumption,
end

open metric

section splitting

/- This section provides the inductive step in the construction of a scheme list bool → α, 
where α is a metric space, of perfect nonempty sets, satisfying 
the disjointness, closure_mono, and vanishing diameter conditions.
If α is complete, then by the results in the scheme_map section, 
this will yield an injective continuous function from (ℕ → bool) to α.
-/

lemma splitting_aux [metric_space α] {C : set α} (hC : perf_nonempty C) 
  (x : α) (xC : x ∈ C) (δ : ℝ) (δ_pos : δ > 0) : perf_nonempty (closure ((ball x δ) ∩ C)) ∧
  bounded (closure ((ball x δ) ∩ C)) ∧ ( diam (closure ((ball x δ) ∩ C)) ≤ 2 * δ) ∧ 
  ((closure ((ball x δ) ∩ C) ⊆ C)) :=
begin
  split, 
  { apply hC.perf_nonempty_of_open_nhd_inter x xC, 
    { apply mem_ball_self δ_pos, },
    apply is_open_ball, },
  split, 
  { rw bounded_closure_iff,
    apply metric.bounded.mono, { apply inter_subset_left, },
    exact bounded_ball, },
  split, 
  { rw diam_closure,
    apply le_trans (diam_mono (inter_subset_left _ C) bounded_ball),
    apply diam_ball,
    linarith, },
  rw hC.2.1.closure_subset_iff,
  apply inter_subset_right,
end

-- The inductive step: we need to "split" a nonempty perfect set into 
-- two disjoint nonempty perfect subsets with small diameters.
lemma splitting [metric_space α] {C : set α} (hC : perf_nonempty C) (ε : ℝ) (ε_pos : ε > 0) : 
  ∃ C₀ C₁ : set α, (perf_nonempty C₀ ∧ bounded C₀ ∧ diam C₀ < ε ∧ C₀ ⊆ C) ∧ 
  (perf_nonempty C₁ ∧ bounded C₁ ∧ diam C₁ < ε ∧ C₁ ⊆ C) ∧ disjoint C₀ C₁ :=
begin
  cases hC.1 with x xC,
  rcases hC.2.2 x xC univ _ with ⟨y,hy,ynex⟩,
  swap, 
  { exact filter.univ_mem },
  cases hy with dum yC,
  clear dum,
  let δ := (min (ε) (dist x y)) / 3,
  have δ_pos : δ > 0, 
  { apply div_pos,
    rw lt_min_iff,
    split, 
    { linarith, },
    rw dist_pos,
    exact ne_comm.mp ynex,
    norm_num, },
  let U₀ := ball x δ,
  let U₁ := ball y δ,
  let C₀ := closure (U₀ ∩ C),
  let C₁ := closure (U₁ ∩ C),
  use [C₀,C₁],
  split, 
  { obtain ⟨h1,h2,h3,h4⟩ := hC.splitting_aux x xC δ δ_pos,
    refine ⟨h1,h2,_,h4⟩,
    apply lt_of_le_of_lt h3,
    dsimp[δ],
    linarith[min_le_left ε (dist x y)], }, split, 
  { obtain ⟨h1,h2,h3,h4⟩ := hC.splitting_aux y yC δ δ_pos,
    refine ⟨h1,h2,_,h4⟩,
    apply lt_of_le_of_lt h3,
    dsimp[δ],
    linarith[min_le_left ε (dist x y)], },
  rw [set.disjoint_iff],
  rintros z ⟨hzx,hzy⟩,
  have hzx' : dist z x ≤ δ, 
  { rw ← mem_closed_ball,
    apply closure_ball_subset_closed_ball,
    apply closure_mono _ hzx,
    apply inter_subset_left, },
  have hzy' : dist z y ≤ δ, 
  { rw ← mem_closed_ball,
    apply closure_ball_subset_closed_ball,
    apply closure_mono _ hzy,
    apply inter_subset_left, },
  rw dist_comm at hzx',
  have := dist_triangle x z y,
  have : dist x y ≤ 2 * δ := by linarith,
  have : δ ≤ (dist x y / 3), 
  { apply div_le_div dist_nonneg, 
    { apply min_le_right, },
    norm_num,
    refl, },
  linarith,
end

end splitting

end perf_nonempty

open function 

--Any nonempty perfect subset of a complete metric space contains a homeomorphic image of 
--the Cantor space ℕ → bool.
theorem cantor_of_perf_nonempty [metric_space α] [complete_space α] {C : set α} 
  (hC : perf_nonempty C) : ∃ f : (ℕ → bool) → α, 
  (range f) ⊆ C ∧ continuous f ∧ injective f:=
begin
  let P := subtype (λ E : set α, perf_nonempty E),
  choose C0 C1 h0 h1 hdisj using @perf_nonempty.splitting α infer_instance,
  let DP : (list bool → P) := begin
    intro s,
    induction s with a s Ds, 
    { exact ⟨C,hC⟩, }, 
    cases a, 
    { use C0 Ds.2 (1/2^s.length:ℝ) (by simp),
      exact (h0 _ _ _).1, },
    use C1 Ds.2 (1/2^s.length:ℝ)  (by simp),
    exact (h1 _ _ _).1,
  end,
  let D : scheme bool α := λ s, (DP s).1,
  have Dperf : ∀ s, perf_nonempty (D s), 
  { intro s,
    exact (DP s).2, },
  have Dclosed : ∀ s, is_closed (D s) := λ s, (Dperf s).2.1,
  have Dnonempty : D.nonempty := λ s, (Dperf s).1,
  have Dmono : D.closure_mono, 
  { intros s a,
    rw (Dclosed (a :: s)).closure_eq,
    cases a; dsimp[D],
    exact (h0 _ _ _).2.2.2,
    exact (h1 _ _ _).2.2.2, },
  have Ddiam : D.vanishing_diam, 
  { apply D.vanishing_diam_of_vanishing_with_length (λ n, 1/2^n) _, 
    { intros s a,
      cases a; dsimp[D],
      exact ⟨(h0 _ _ _).2.1,(h0 _ _ _).2.2.1⟩,
      exact ⟨(h1 _ _ _).2.1,(h1 _ _ _).2.2.1⟩, },
    simp only [← one_div_pow],
    apply tendsto_pow_at_top_nhds_0_of_lt_1; norm_num, },
  have f := D.map_from_closed_mono_and_vanishing_diam Dnonempty Dmono Ddiam,
  use f.map, split, 
  { rintros y ⟨x, rfl⟩,
    exact f.mem x 0, },
  split, { exact D.map_cts_of_vanishing_diam f Ddiam, },
  apply D.map_inj_of_disjoint,
  intros s a b aneb,
  cases b, 
  { rw bool.eq_tt_of_ne_ff aneb,
    dsimp[D],
    apply disjoint.symm _ ,
    apply hdisj, },
  rw bool.eq_ff_of_ne_tt aneb,
  dsimp[D],
  apply hdisj,
end

section kernel

variable [topological_space α]

/- Any closed subset of a second countable space can be written as 
the union of a perfect set and a countable set. 
The perfect set is sometimes called the ``perfect kernel'' of the closed set. 
This result is sometimes called ``The Cantor-Bendixson Theorem''.
In fact this conclusion can easily be strengthened in a number of ways which we do not need: 
V is open, V and D are disjoint, and this decomposition is the unique one with these properties.-/
theorem ctble_union_perfect_of_closed [second_countable_topology α] {C : set α} (hclosed : is_closed C) : 
∃ V D : set α, (V.countable) ∧ (perfect D) ∧ (C = V ∪ D) :=
begin
  have := topological_space.exists_countable_basis α,
  rcases this with ⟨b,bct,bnontrivial,bbasis⟩,
  let v := {U ∈ b | (U ∩ C).countable},
  let V := ⋃ U ∈ v, U,
  let D := C ∩ Vᶜ, --C \ V did not work
  have Vct : (V ∩ C).countable, { 
    simp[V,Union_inter],
    apply set.countable.bUnion, 
    { apply @set.countable.mono _ _ b, 
      { apply set.inter_subset_left, },
      exact bct, },
    apply set.inter_subset_right, },
  use [V ∩ C,D],
  split, swap, split, split, 
  { apply is_closed.inter hclosed,
    rw is_closed_compl_iff,
    apply is_open_bUnion,
    rintros U ⟨Ub,-⟩,
    exact is_topological_basis.is_open bbasis Ub, }, 
  { intros x xD E xE,
    have : ¬ (E ∩ D).countable, 
    { intro h,
      obtain ⟨U,hUb,xU,hU⟩ : ∃ U ∈ b, x ∈ U ∧ U ⊆ E, 
      { exact (is_topological_basis.mem_nhds_iff bbasis).mp xE, },
      have : U ∈ v, 
      { use hUb,
        dsimp,
        apply @countable.mono _ _ ((E ∩ D) ∪ (V ∩ C)), 
        { rintros y ⟨yU,yC⟩,
          by_cases y ∈ V, 
          { right,
            exact ⟨h,yC⟩, },
          left,
          split, 
          { exact hU yU, },
          exact ⟨yC, h⟩, },
        apply countable.union h Vct, },
      apply xD.2,
      exact mem_bUnion this xU, },
    by_contradiction,
    push_neg at h,
    apply this,
    have : E ∩ D ⊆ {x}, {exact h},
    apply countable.mono this,
    apply set.countable_singleton, }, 
  { dsimp[D],
    rw[inter_comm,inter_union_compl], },
  assumption,
end

-- If the closed set in the previous theorem is uncountable, the kernel must be nonempty perfect
theorem perf_nonempty_of_closed_unctble [second_countable_topology α] {C : set α} 
  (hclosed : is_closed C) (hunc : ¬ C.countable) : ∃ D : set α, (perf_nonempty D) ∧ (D ⊆ C) :=
begin
  rcases ctble_union_perfect_of_closed hclosed with ⟨V,D,Vct,Dperf,VD⟩,
  use D,
  split, 
  { split, 
    { rw ← ne_empty_iff_nonempty,
      by_contradiction,
      rw [h, union_empty] at VD,
      rw VD at hunc,
      contradiction, },
    exact Dperf, },
  rw VD,
  apply subset_union_right,
end

/- This combines the above version of Cantor-Bendixson with cantor_of_perf_nonempty.
This result itself is sometimes called ``The Cantor-Bendixson Theorem"-/
theorem cantor_of_closed_unc [polish_space α] {C : set α} 
  (hclosed : is_closed C) (hunc : ¬ C.countable) : 
  ∃ f : (ℕ → bool) → α, (range f) ⊆ C ∧ continuous f ∧ function.injective f := 
begin
  letI := upgrade_polish_space α,
  rcases perf_nonempty_of_closed_unctble hclosed hunc with ⟨D, Dperf, DC⟩,
  rcases cantor_of_perf_nonempty Dperf with ⟨f,hf⟩,
  use f,
  simp[hf],
  exact hf.1.trans DC,
end

end kernel