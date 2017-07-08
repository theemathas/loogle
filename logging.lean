import system.io

section
  variable [io.interface]
  private def log_io (s : string) : io unit := do
    h ← io.mk_file_handle "log.txt" io.mode.append,
    io.fs.put_str_ln h s,
    io.fs.close h
end

meta def log (s : string) : tactic unit := tactic.run_io (λ ioi, @log_io ioi s)