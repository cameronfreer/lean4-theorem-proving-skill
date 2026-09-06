import Gate.A

-- Lives under a custom `srcDir = "src"`: its module name is `Custom.Inner`,
-- not `src.Custom.Inner`, so a source path (not a hand-derived name) is the
-- only safe way to address it.
theorem Custom.inner : Gate.value = 1 := rfl
