#r @"netstandard.dll"
#load @".paket\load\main.group.fsx"

open Aardvark.Base

module QR =
    [<AutoOpen>]
    module private Helpers = 
        let inline tiny (eps : float) (v : float) =
            abs v <= eps
        
        let identity (rows : int) (cols : int) =
            Array2D.init rows cols (fun ri ci ->
                if ri = ci then 1.0
                else 0.0
            )

        let applyGivens (mat : float[,]) (c : int) (r : int) (cos : float) (sin : float) =
            let cols = mat.GetLength(0)
            // adjust affected elements
            for ci in 0 .. cols - 1 do
                let A = mat.[ci, c]
                let B = mat.[ci, r]
                mat.[ci, c] <-  cos * A + sin * B
                mat.[ci, r] <- -sin * A + cos * B
       
    let decompose (eps : float) (mat : float[,]) =
        let rows = mat.GetLength(0)
        let cols = mat.GetLength(1)
        
        let R = Array2D.copy mat
        let Q = identity rows rows

        for c in 0 .. cols - 1 do
            // wiki performs this loop backwards (should not really matter)
            for r in c + 1 .. rows - 1 do
                let vcc = R.[c,c] // important since R.[c,c] changes
                let vrc = R.[r,c]

                // if the dst-element is not already zero then make it zero
                if not (tiny eps vrc) then

                    // find givens rotation
                    let rho = float (sign vcc) * sqrt (vcc * vcc + vrc * vrc)
                    let cos = vcc / rho
                    let sin = vrc / rho
                    
                    // adjust affected elements
                    for ci in 0 .. cols - 1 do
                        let A = R.[c,ci]
                        let B = R.[r,ci]
                        R.[c,ci] <-  cos * A + sin * B
                        R.[r,ci] <- -sin * A + cos * B
                        
                    // adjust the resulting Q matrix
                    applyGivens Q c r cos sin

        Q, R
    
    



[<AutoOpen>]
module private MatrixUtils =

    let tolerance = 1E-8

    let applyGivens (mat : float[,]) (c : int) (r : int) (cos : float) (sin : float) =
        let cols = mat.GetLength(0)
        // adjust affected elements
        for ci in 0 .. cols - 1 do
            let A = mat.[ci, c]
            let B = mat.[ci, r]
            mat.[ci, c] <-  cos * A + sin * B
            mat.[ci, r] <- -sin * A + cos * B
       

    let print (m : float[,]) =
        let rows = m.GetLength(0)
        let cols = m.GetLength(1)

        for ri in 0 .. rows - 1 do
            for ci in 0 .. cols - 1 do
                printf "%.3f " m.[ri,ci]
            printfn ""



    let identity (rows : int) (cols : int) =
        Array2D.init rows cols (fun ri ci ->
            if ri = ci then 1.0
            else 0.0
        )

    let mul (A : float[,]) (B : float[,]) =
        let r = A.GetLength(0)
        let c = B.GetLength(1)

        assert(A.GetLength(1) = B.GetLength(0))
        let inner = A.GetLength(1)

        Array2D.init r c (fun r c ->
            let mutable sum = 0.0
            for i in 0 .. inner - 1 do
                sum <- sum + A.[r, i] * B.[i, c]
            sum
        )

    let transpose (A : float[,]) =
        let r = A.GetLength(1)
        let c = A.GetLength(0)
            
        Array2D.init r c (fun r c ->
            A.[c,r]
        )
        
    let distanceMinMaxAvg (A : float[,]) (B : float[,]) =
        let mutable dmin = System.Double.PositiveInfinity
        let mutable dmax = 0.0
        let mutable dsum = 0.0


        let mutable maxEntry = 0.0

        for r in 0 .. A.GetLength(0) - 1 do
            for c in 0 .. A.GetLength(1) - 1 do
                let d = abs (A.[r,c] - B.[r,c])
                dmin <- min dmin d
                dmax <- max dmax d
                dsum <- dsum + d
                maxEntry <- max maxEntry (max (abs A.[r,c]) (abs B.[r,c]))

        if maxEntry = 0.0 then
            (0.0, 0.0, 0.0)
        else
            (dmin / maxEntry, dmax / maxEntry, dsum / (maxEntry * float (A.GetLength(0) * A.GetLength(1))))
            
    let rightUpper (A : float[,]) =
        let mutable dmin = System.Double.PositiveInfinity
        let mutable dmax = 0.0
        let mutable dsum = 0.0
        if A.GetLength(0) > 1 && A.GetLength(1) > 1 then
            for r in 0 .. A.GetLength(0) - 1 do
                for c in 0 .. min (r - 1) (A.GetLength(1) - 1) do
                    let d = abs A.[r,c]
                    dmin <- min dmin d
                    dmax <- max dmax d
                    dsum <- dsum + d
            (dmin, dmax, dsum / float (A.GetLength(0) * A.GetLength(1)))
        else
            (0.0, 0.0, 0.0)

    let arr2d (rows : int) (cols : int) (data : 'a[]) =
        Array2D.init rows cols (fun r c ->
            let i = c + r * cols
            data.[i]
        )

module QRTest =
    open System.Collections.Generic

    let rand = System.Random()

    let random () =
        let rows = rand.Next(64) + 1
        let cols = rand.Next(64) + 1

        Array2D.init rows cols (fun r c ->
            rand.NextDouble() * 20.0 - 10.0
        )

    let specialCases =
        [|
            // zero matrix
            fun r c -> Array2D.zeroCreate r c
            
            //identity
            identity

            // ortho
            fun r c ->
                let s = max r c
                let iter = rand.Next(10 * s) + 2
                let mat = identity s s

                if s > 1 then
                    for i in 1 .. iter do 
                        let mutable c = rand.Next(s)
                        let mutable r = rand.Next(s)
                        while r = c do r <- rand.Next(s)

                        if c > r then
                            let t = c
                            c <- r
                            r <- t

                        let angle = rand.NextDouble() * System.Math.PI * 2.0

                        applyGivens mat c r (cos angle) (sin angle)
                
                mat
        |]

    let randomSpecial () =
        let rows = rand.Next(10) + 1
        let cols = rand.Next(10) + 1
        let case = specialCases.[rand.Next(specialCases.Length)]
        case rows cols
        

    let check (eps : float) (mat : float[,]) =
        let Q, R = QR.decompose eps mat
        let mutable valid = true

        let min, max, avg = rightUpper R
        if max > tolerance then 
            printfn "not right upper: { size = [%d, %d]; min = %e; max = %e; avg = %e }" (mat.GetLength(0)) (mat.GetLength(1)) min max avg
            print R
            printfn "input"
            print mat
            valid <- false

        let (min, max, avg) = distanceMinMaxAvg (mul Q (transpose Q)) (identity (Q.GetLength(0)) (Q.GetLength(1)))
        if max > tolerance then 
            printfn "not ortho: { size = [%d, %d]; min = %e; max = %e; avg = %e }" (Q.GetLength(0)) (Q.GetLength(1)) min max avg
            print Q
            printfn "Q * Qt"
            print (mul Q (transpose Q))
            valid <- false

        let test = mul Q R
        let (min, max, avg) = distanceMinMaxAvg mat test
        if max > tolerance then
            printfn "invalid: { size = [%d, %d]; min = %e; max = %e; avg = %e }" (mat.GetLength(0)) (mat.GetLength(1)) min max avg
            printfn "in:"
            print mat
            printfn "out:"
            print test
            valid <- false
        else
            printfn "valid: { size = [%d, %d]; min = %e; max = %e; avg = %e }" (mat.GetLength(0)) (mat.GetLength(1)) min max avg

        valid
        
    let errorMetrics (iter : int) =
        let buckets = SortedDictionary<int, ref<float * int>>()

        let add (value : float) =
            let e = floor (log10 value) |> int
            let ref = 
                match buckets.TryGetValue e with
                    | (true, ref) ->
                        ref
                    | _ ->
                        let r = ref (0.0, 0)
                        buckets.Add(e, r)
                        r
            let (avg, oc) = !ref
            let nc = oc + 1
            let navg = avg * (float oc / float nc) + value * (1.0 / float nc)
            ref := (navg, nc)

        
        let mutable error = false
        for i in 1 .. iter do
            if not error then
                let mat = if rand.NextDouble() > 0.1 then random() else randomSpecial()
                let Q, R = QR.decompose 1.0E-20 mat

                let (min, max, avg) = rightUpper R
                if max > tolerance then 
                    printfn "not right upper: { size = [%d, %d]; min = %e; max = %e; avg = %e }" (mat.GetLength(0)) (mat.GetLength(1)) min max avg
                    print R
                    printfn "input"
                    print mat
                    error <- true

                let (min, max, avg) = distanceMinMaxAvg (mul Q (transpose Q)) (identity (Q.GetLength(0)) (Q.GetLength(1)))
                if max > tolerance then 
                    printfn "not ortho: { size = [%d, %d]; min = %e; max = %e; avg = %e }" (Q.GetLength(0)) (Q.GetLength(1)) min max avg
                    print Q
                    printfn "Q * Qt"
                    print (mul Q (transpose Q))
                    error <- true

                let test = mul Q R
                let (min, max, avg) = distanceMinMaxAvg mat test
                printfn "valid: { size = [%d, %d]; min = %e; max = %e; avg = %e }" (mat.GetLength(0)) (mat.GetLength(1)) min max avg
                add max

        if not error then
            let histogram = 
                buckets |> Seq.toArray |> Array.map (fun (KeyValue(e, r)) ->
                    let f = 10.0 ** float e
                    let (avg,cnt) = !r
                    let v = avg / f
                    (v, e, cnt)
                )

            let table =
                [|
                    histogram |> Array.map (fun (_,e,_) -> if e = System.Int32.MinValue then "0" else sprintf "e%d" e)
                    histogram |> Array.map (fun (v,e,_) -> if e = System.Int32.MinValue then "" else sprintf "%.4f" v)
                    histogram |> Array.map (fun (_,_,c) -> sprintf "%.2f%%" (100.0 * float c / float iter))
                |]

            let printTable (arr : string[][]) =
                let maxLength =
                    arr |> Seq.collect (fun row ->
                        row |> Seq.map (fun str -> str.Length)
                    )
                    |> Seq.max

                let pad (str : string) =
                    if str.Length < maxLength then
                        let diff = maxLength - str.Length
                        let left = diff / 2
                        let right = diff - left
                        System.String(' ', left) + str + System.String(' ', right)
                    else
                        str
            
                let totalLength = arr.[0].Length * (maxLength + 4) //+ (arr.[0].Length - 1) * 3
                let line = System.String('-', totalLength)
                printfn "%s" line

                for row in arr do
                    printf "|"
                    for e in row do
                        printf " %s | " (pad e)
                    printfn ""
                
                printfn "%s" line
                ()

            printTable table

    let validateSpecial(iter : int) =
        let mutable valid = true
        printfn "special cases: "
        for i in 1 .. iter do
            let m = randomSpecial()
            valid <- valid && check 1.0E-20 m
        

    let validate(iter : int) =
        let mutable valid = true
        printfn "special cases: "
        for i in 1 .. 100 do
            let m = randomSpecial()
            valid <- valid && check 1.0E-20 m
        
        
        printfn "general cases: "
        for i in 1 .. iter do
            let m = random()
            valid <- valid && check 1.0E-20 m

    // https://de.wikipedia.org/wiki/Givens-Rotation
    let wikiExample() =
        let A = 
            arr2d 4 2 [|
                3.0; 5.0
                0.0; 2.0
                0.0; 0.0
                4.0; 5.0
            |] 

        let Qexpected =
            arr2d 4 4 [|
                3.0 / 5.0;      4.0 / (5.0 * sqrt 5.0);         0.0;        -8.0 / (5.0 * sqrt 5.0)
                0.0;            2.0 / (sqrt 5.0);               0.0;        1.0 / (sqrt 5.0)
                0.0;            0.0;                            1.0;        0.0
                4.0 / 5.0;      -3.0/(5.0 * sqrt 5.0);          0.0;        6.0/(5.0 * sqrt 5.0)
            |]

        let Rexpected =
            arr2d 4 2 [|
                5.0; 7.0
                0.0; sqrt 5.0
                0.0; 0.0
                0.0; 0.0
            |]

        printfn "A: "
        print A

        printfn "Qexpected:" 
        print Qexpected

        let Q, R = QR.decompose 1E-20 A
        printfn "Q: "
        print Q
    
        printfn "Rexpected:" 
        print Rexpected

        printfn "R: "
        print R
        

