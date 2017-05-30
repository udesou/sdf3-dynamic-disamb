(**
 * Copyright (c) 2015, Facebook, Inc.
 * All rights reserved.
 *
 * This source code is licensed under the BSD-style license found in the
 * LICENSE file in the "hack" directory of this source tree. An additional grant
 * of patent rights can be found in the PATENTS file in the same directory.
 *
 *)

let save options =
  let root = Options.root options in
  let config_file = Server_files_js.config_file root in
  let config = FlowConfig.get config_file in
  (config_file, config)

let restore (config_file, config) =
  FlowConfig.restore (config_file, config)

(* As for [Daemon.register_entry_point], this should stay
   at toplevel, in order to be executed before
   [Daemon.check_entry_point]. *)
let entry = Worker.register_entry_point ~restore

(* Saves the default GC settings, which are restored by the workers. Workers can
 * have more relaxed GC configs as they are short-lived processes, and this
 * prevents the workers from inheriting GC settings the master needs. *)
let gc_control = Gc.get ()

let make options heap_handle =
  Worker.make
    ?call_wrapper:None
    ~saved_state: (save options)
    ~entry
    ~nbr_procs: (Options.max_workers options)
    ~gc_control
    ~heap_handle
