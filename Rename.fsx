#r @"netstandard.dll"
#load @".paket\load\main.group.fsx"

open System.IO
open System.Text.RegularExpressions


let renameFiles (folder : string) (pattern : string) (replacement : Match -> Option<string>) =
    let files = Directory.GetFiles(folder, "*", SearchOption.AllDirectories)

    let rx = Regex pattern
    for f in files do
        let name = Path.GetFileNameWithoutExtension f
        let m = rx.Match name
        if m.Success then
            let newName = rx.Replace(name, MatchEvaluator(fun m -> match replacement m with | Some v -> v | _ -> m.Value))
            let newPath = Path.Combine(Path.GetDirectoryName(f), newName + Path.GetExtension f)
            if f <> newPath then
                //printfn "%s -> %s" (Path.GetFileName f) (Path.GetFileName newPath)
                File.Move(f, newPath)
