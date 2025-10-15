let version =
  let append_version v = v |> Build_info.V1.Version.to_string |> Printf.sprintf "v%s" in
  Option.fold (Build_info.V1.version ()) ~none:"development" ~some:append_version
;;
