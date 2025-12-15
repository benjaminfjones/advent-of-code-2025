
namespace Grid

variable {α: Type} [Inhabited α]

structure Grid α where
  data: Array (Array α)
  validRows: 0 < data.size
  validCols: ∀ i, (h : 0 ≤ i ∧ i < data.size) → 0 < (data[i]'h.right).size
  nrows: Nat
  ncols: Nat
  nrowEqn: nrows = data.size
  ncolEqn: ∀ i, (h : 0 ≤ i ∧ i < data.size) → ncols = (data[i]'h.right).size

def Grid.replicate (rows cols: Nat) (a: α) : Grid α :=
  sorry

instance : GetElem (Grid α) (Nat × Nat) α (fun g rc => (0 ≤ rc.fst ∧ rc.fst < g.nrows) ∧ (0 ≤ rc.snd ∧ rc.snd < g.ncols)) where
  getElem g rc valid := 
    have hr : rc.fst < g.data.size := by
      rw [g.nrowEqn] at valid
      exact valid.left.right
    have hc : rc.snd < (g.data[rc.fst]'hr).size := by
      have : g.ncols = (g.data[rc.fst]'hr).size := by
        refine g.ncolEqn rc.fst ⟨?_, ?_⟩
        . exact valid.left.left
        . rw [g.nrowEqn] at valid
          exact valid.left.right
      rw [this] at valid
      exact valid.right.right
    (g.data[rc.fst]'hr)[rc.snd]'hc

instance : GetElem? (Grid α) (Nat × Nat) α (fun g rc => (0 ≤ rc.fst ∧ rc.fst < g.nrows) ∧ (0 ≤ rc.snd ∧ rc.snd < g.ncols)) where
  getElem? g rc := (g.data[rc.fst]?) >>= λ row => row[rc.snd]?
  getElem! g rc := g.data[rc.fst]![rc.snd]!

end Grid

