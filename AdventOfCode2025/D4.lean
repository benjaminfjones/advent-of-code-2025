
namespace Grid

variable {α: Type} [Inhabited α]

structure Grid α where
  data: Array (Array α)
  validRows: 0 < data.size
  validCols: ∀ i, (h: i < data.size) → 0 < (data[i]'h).size
  nrows: Nat
  ncols: Nat
  nrowEqn: nrows = data.size
  ncolEqn: ∀ i, (h : i < data.size) → ncols = (data[i]'h).size

def Grid.replicate (rows cols: Nat) (a: α) (hr: 0 < rows) (hc: 0 < cols) : Grid α :=
  let row := Array.replicate cols a
  let data := Array.replicate rows row
  {
    data := data,
    nrows := rows,
    ncols := cols,
    /- validRows := by grind  -- size_replicate has a grind attribute -/
    validRows := by
      have : data.size = rows := by apply Array.size_replicate
      rw [this]
      exact hr,
    /- validCols := by grind -/
    validCols := by
      intro i h
      rw [Array.getElem_replicate, Array.size_replicate]
      exact hc
    nrowEqn := by grind
    ncolEqn := by grind
  }

instance : GetElem (Grid α) (Nat × Nat) α (fun g rc => rc.fst < g.nrows ∧ rc.snd < g.ncols) where
  getElem g rc valid :=
    have hr : rc.fst < g.data.size := by
      rw [g.nrowEqn] at valid
      exact valid.left
    have hc : rc.snd < (g.data[rc.fst]'hr).size := by
      have : g.ncols = (g.data[rc.fst]'hr).size := by
        apply g.ncolEqn rc.fst
      rw [this] at valid
      exact valid.right
    (g.data[rc.fst]'hr)[rc.snd]'hc

instance : GetElem? (Grid α) (Nat × Nat) α (fun g rc => rc.fst < g.nrows ∧ rc.snd < g.ncols) where
  getElem? g rc := (g.data[rc.fst]?) >>= λ row => row[rc.snd]?
  getElem! g rc := g.data[rc.fst]![rc.snd]!

def Grid.set (g: Grid α) (idx: Nat × Nat) (v: α) (h: idx.fst < g.nrows ∧ idx.snd < g.ncols) : Grid α := sorry

end Grid

