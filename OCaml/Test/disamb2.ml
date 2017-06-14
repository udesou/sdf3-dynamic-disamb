let n = Script_int.to_int64 kind n in
              Lwt.return
                (e1 >>? fun p ->
                 e2 >>? fun res ->
                 e3)