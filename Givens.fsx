#r @"netstandard.dll"
#load @".paket\load\main.group.fsx"

open System.Runtime.CompilerServices
open Microsoft.FSharp.NativeInterop
open Aardvark.Base
open Aardvark.Base.Sorting
#nowarn "9"
#nowarn "51"

module QR =
    open System.Web.UI.WebControls

    [<AutoOpen>]
    module private Helpers = 
        let inline tiny (eps : 'a) (v : 'a) =
            abs v <= eps
        
        let identity (rows : int) (cols : int) =
            Array2D.init rows cols (fun ri ci ->
                if ri = ci then 1.0
                else 0.0
            )

        let identityMat (rows : int) (cols : int) =
            let mat = Matrix<float>(int64 cols, int64 rows)
            mat.SetByCoord(fun (c : V2l) ->
                if c.X = c.Y then 1.0
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

        let applyGivensTransposed (mat : float[,]) (c : int) (r : int) (cos : float) (sin : float) =
            let rows = mat.GetLength(1)
            // adjust affected elements
            for ri in 0 .. rows - 1 do
                let A = mat.[c, ri]
                let B = mat.[r, ri]
                mat.[c, ri] <-  cos * A + sin * B
                mat.[r, ri] <- -sin * A + cos * B
            
        let inline applyGivensMat (mat : NativeMatrix<float>) (c : int) (r : int) (cos : float) (sin : float) =
            let ptrQ = NativePtr.toNativeInt mat.Pointer
            let dcQ = nativeint sizeof<float> * nativeint mat.DX
            let drQ = nativeint sizeof<float> * nativeint mat.DY
            let cols = int mat.SX

            let mutable p0 = ptrQ + nativeint c * dcQ 
            let mutable p1 = ptrQ + nativeint r * dcQ      
            // adjust affected elements
            for ci in 0 .. cols - 1 do
                let A = NativeInt.read<float> p0 //mat.[ci, c]
                let B = NativeInt.read<float> p1 //mat.[ci, r]

                //mat.[ci, c] <-  cos * A + sin * B
                //mat.[ci, r] <- -sin * A + cos * B
                NativeInt.write p0 ( cos * A + sin * B )
                NativeInt.write p1 (-sin * A + cos * B )

                p0 <- p0 + drQ
                p1 <- p1 + drQ

        let inline applyGivensMat32 (mat : NativeMatrix<float32>) (c : int) (r : int) (cos : float32) (sin : float32) =
            let ptrQ = NativePtr.toNativeInt mat.Pointer
            let dcQ = nativeint sizeof<float32> * nativeint mat.DX
            let drQ = nativeint sizeof<float32> * nativeint mat.DY
            let cols = int mat.SX

            let mutable p0 = ptrQ + nativeint c * dcQ 
            let mutable p1 = ptrQ + nativeint r * dcQ      
            // adjust affected elements
            for ci in 0 .. cols - 1 do
                let A = NativeInt.read<float32> p0 //mat.[ci, c]
                let B = NativeInt.read<float32> p1 //mat.[ci, r]

                //mat.[ci, c] <-  cos * A + sin * B
                //mat.[ci, r] <- -sin * A + cos * B
                NativeInt.write p0 ( cos * A + sin * B )
                NativeInt.write p1 (-sin * A + cos * B )

                p0 <- p0 + drQ
                p1 <- p1 + drQ

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


    let bidiagonalize (eps : float) (mat : float[,]) =
        let rows = mat.GetLength(0)
        let cols = mat.GetLength(1)
        
        let B = Array2D.copy mat
        let U = identity rows rows
        let Vt = identity cols cols

        for i in 0 .. cols - 1 do
            // wiki performs this loop backwards (should not really matter)
            let c = i
            let r0 = i
            for r1 in r0 + 1 .. rows - 1 do
                let vcc = B.[r0,c] // important since R.[c,c] changes
                let vrc = B.[r1,c]

                // if the dst-element is not already zero then make it zero
                if not (tiny eps vrc) then

                    // find givens rotation
                    let rho = float (sign vcc) * sqrt (vcc * vcc + vrc * vrc)
                    let cos = vcc / rho
                    let sin = vrc / rho
                    
                    // adjust affected elements
                    for ci in 0 .. cols - 1 do
                        let a = B.[r0,ci]
                        let b = B.[r1,ci]
                        B.[r0,ci] <-  cos * a + sin * b
                        B.[r1,ci] <- -sin * a + cos * b
                        
                    // adjust the resulting Q matrix
                    applyGivens U r0 r1 cos sin
                    
            let r = i
            let c0 = r + 1
            for c1 in c0 + 1 .. cols - 1 do
                let vcc = B.[r,c0] // important since R.[c,c] changes
                let vrc = B.[r,c1]

                // if the dst-element is not already zero then make it zero
                if not (tiny eps vrc) then

                    // find givens rotation
                    let rho = if vcc = 0.0 then abs vrc else float (sign vcc) * sqrt (vcc * vcc + vrc * vrc)
                    let sin = vrc / rho
                    let cos = vcc / rho

                    // adjust affected elements
                    for ri in 0 .. rows - 1 do
                        let a = B.[ri, c0]
                        let b = B.[ri, c1]
                        B.[ri, c0] <- cos * a + sin * b
                        B.[ri, c1] <- -sin * a + cos * b
                        
                    // adjust the resulting Q matrix
                    applyGivensTransposed Vt c0 c1 cos sin

        U, B, Vt

    module Array2D =
        let toSeq (a : 'a[,]) =
            seq {
                for i0 in 0 .. a.GetLength(0) - 1 do
                    for i1 in 0 .. a.GetLength(1) - 1 do
                        yield a.[i0, i1]
            }

    let printTable (sep : bool) (arr : string[,]) =
        
        let maxLength =
            arr |> Array2D.toSeq |> Seq.map (fun str -> str.Length) |> Seq.max

        let pad (str : string) =
            if str.Length < maxLength then
                let diff = maxLength - str.Length
                let left = diff / 2
                let right = diff - left
                System.String(' ', left) + str + System.String(' ', right)
            else
                str
            
        let totalLength = arr.GetLength(1) * (maxLength + 4) //+ (arr.[0].Length - 1) * 3
        
        let line = System.String('-', totalLength)
        if sep then printfn "%s" line

        for r in 0 .. arr.GetLength(0) - 1 do
            if sep then printf "|"
            for c in 0 .. arr.GetLength(1) - 1 do
                let e = arr.[r,c]
                if sep then printf " %s | " (pad e)
                else printf " %s " (pad e)
            printfn ""
                
        if sep then printfn "%s" line
        ()


    let print (m : float[,]) =
        m |> Array2D.map (sprintf "%.3f") |> printTable false

    //let svdBidiagonal (eps : float) (U : float[,]) (mat : float[,]) (Vt : float[,]) =
    //    let rows = mat.GetLength(0)
    //    let cols = mat.GetLength(1)
    //    if cols < 2 then
    //        failwith "think"
    //    else

    //        let U = Array2D.copy U
    //        let B = Array2D.copy mat
    //        let Vt = Array2D.copy Vt

    //        let inline sgn v = if v < 0.0 then -1.0 else 1.0

    //        /// wilkinson shift for symmetric 2x2 matrix
    //        /// | a | b |
    //        /// | b | c |
    //        let wilkinson (a : float) (b : float) (c : float) =
    //            if tiny eps b then
    //                c
    //            else
    //                let s = (a - c) / 2.0
    //                c - (sgn s * b * b) / (abs s + sqrt (s*s + b*b))

    //        let size = min cols rows

    //        let mutable lastErr = System.Double.PositiveInfinity
    //        let mutable err = System.Double.MaxValue
    //        let mutable iter = 0
    //        while lastErr <> err do
    //            // https://web.stanford.edu/class/cme335/lecture6.pdf
    //            // http://www.math.cornell.edu/~web6140/TopTenAlgorithms/QRalgorithm.html

    //            // Step 1
    //            // find wilkinson shift for T = Bt * B (symmetric tridiagonal)
    //            // T € cols x cols
    //            // tij = sum 0 (rows-1) (fun x -> Bt.[i,x] * B.[x,j])
    //            // tij = sum 0 (rows-1) (fun x -> B.[x,i] * B.[x,j])

    //            // bidiagonal
    //            // i > j        -> B.[i,j] = 0
    //            // i < j - 1    -> B.[i,j] = 0

    //            // i = j
    //            // tii = sum 0 rows (fun x -> B.[x,i] * B.[x,i])
    //            // tii = B.[i,i]^2 + B.[i,i+1]*B.[i,i+1]

    //            // i < j
    //            // tij = sum 0 rows (fun x -> B.[x,i] * B.[x,j])

    //            let my =
    //                if rows < cols then
    //                    let f1 = B.[rows-2, rows-1]
    //                    let d2 = B.[rows-1, rows-1]
    //                    let f2 = B.[rows-1, rows]

    //                    let t00 = f1*f1 + d2*d2
    //                    let t10 = d2*f2
    //                    let t11 = f2*f2

    //                    wilkinson t00  t10 t11
    //                else
    //                    let f0 = B.[cols-3, cols-2]
    //                    let d1 = B.[cols-2, cols-2]
    //                    let f1 = B.[cols-2, cols-1]
    //                    let d2 = B.[cols-1, cols-1]

    //                    let t00 = f0*f0 + d1*d1
    //                    let t10 = d1*f1
    //                    let t11 = f1*f1 + d2*d2

    //                    wilkinson t00 t10 t11

    //            //B.[rows - 1
                
    //            for k in 
    //            let mutable rs = min rows (cols - 1) - 1

    //            while rs >= 0 && tiny 1E-8 B.[rs,rs + 1] do
    //                rs <- rs - 1

    //            //printfn "start: %A" rs
    //            if rs > 0 then
    //                let t00 = 
    //                    if rs > 0 then B.[rs-1,rs] * B.[rs-1, rs] + B.[rs,rs] * B.[rs,rs]
    //                    else B.[rs,rs] * B.[rs,rs]

    //                let t10 = B.[rs,rs] * B.[rs,rs+1]

    //                let y = B.[rs-1,rs-1]
    //                let g = B.[rs-1,rs]
    //                let h = B.[rs,rs]
    //                let f = ((y - z) * (y + z) + (g - h) * (g + h)) / (2.0 * h * y)
    //                let g = Fun.Pythag(f, 1.0)
    //                let f = ((x - z) * (x + z) + h * ((y / (f + ((f >= 0.0) ? abs(g) : -abs(g)))) - h)) / x

    //                // shift T to T - my*I
    //                let ts00 = B.[rs,rs] //t00 - my
    //                let ts10 = B.[rs,rs+1] //t10
                
    //                // Step 2
    //                if not (tiny eps ts10) then
    //                    // find givens rotation for shifted T
    //                    let rho = sgn ts00 * sqrt (ts00 * ts00 + ts10 * ts10)
    //                    let cos = ts00 / rho
    //                    let sin = ts10 / rho
                    
    //                    // adjust affected elements
    //                    for ri in 0 .. rows - 1 do
    //                        let a = B.[ri,rs]
    //                        let b = B.[ri,rs+1]
    //                        B.[ri,rs] <-    cos * a + sin * b
    //                        B.[ri,rs+1] <- -sin * a + cos * b

    //                    applyGivensTransposed Vt rs (rs+1) cos sin

    //                // Step 3
    //                let mutable br = rs+1
    //                let mutable bc = rs


    //                while br < rows && bc < cols do
    //                    let r0 = br - 1
    //                    let r1 = br
                    
             
    //                    let v0 = B.[r0, bc]
    //                    let v1 = B.[r1, bc]
    //                    if not (tiny eps v1) then

    //                        // find givens rotation
    //                        let rho = sgn v0 * sqrt (v0 * v0 + v1 * v1)
    //                        let cos = v0 / rho
    //                        let sin = v1 / rho
                    
    //                        // adjust affected elements
    //                        for ci in 0 .. cols - 1 do
    //                            let a = B.[r0,ci]
    //                            let b = B.[r1,ci]
    //                            B.[r0,ci] <-  cos * a + sin * b
    //                            B.[r1,ci] <- -sin * a + cos * b
                        
    //                        applyGivens U r0 r1 cos sin
                    
    //                    let c0 = r0 + 1
    //                    let c1 = r0 + 2
    //                    if c1 < cols then
    //                        let v0 = B.[r0, c0]
    //                        let v1 = B.[r0, c1]
    //                        if not (tiny eps v1) then
    //                            // find givens rotation
    //                            let rho = sgn v0 * sqrt (v0 * v0 + v1 * v1)
    //                            let cos = v0 / rho
    //                            let sin = v1 / rho

    //                            // adjust affected elements
    //                            for ri in 0 .. rows - 1 do
    //                                let a = B.[ri, c0]
    //                                let b = B.[ri, c1]
    //                                B.[ri,c0] <-  cos * a + sin * b
    //                                B.[ri,c1] <- -sin * a + cos * b
                        
    //                            applyGivensTransposed Vt c0 c1 cos sin

    //                    //br <- rows
    //                    br <- br + 1
    //                    bc <- bc + 1
                    
    //                let mutable e = 0.0
    //                for r in 0 .. rows - 1 do
    //                    if r < cols - 1 then
    //                        let v = B.[r, r+1]
    //                        if tiny eps v then
    //                            printfn "tiny"
    //                        e <- max e (abs v)

    //                lastErr <- err
    //                err <- e
    //                iter <- iter + 1

    //                printfn "%d: %.3e" iter err

    //            //printfn "B"
    //            //print B
             




    //            // T = Bt * B
    //            // T € cols * cols
                
    //            // let t r c = sum 0 (rows-1) (fun k -> Bt.[r, k] * B.[k, c])
    //            // let t r c = sum 0 (rows-1) (fun k -> B.[k, r] * B.[k, c])

    //            // wlog: r <= c
    //            // let t r c = sum r (rows-1) (fun k -> B.[k, r] * B.[k, c])
                
                

    //        U, B, Vt, err

        
    

    let decomposeNative (eps : float) (pQ : NativeMatrix<float>) (pR : NativeMatrix<float>) =
        let rows = int pR.SY
        let cols = int pR.SX

        // pQ <- identity
        pQ.SetByCoord (fun (v : V2i) -> if v.X = v.Y then 1.0 else 0.0)
        
        let sa = nativeint sizeof<float>
        let drR = nativeint pR.DY * sa
        let dcR = nativeint pR.DX * sa

        let mutable pc0 = NativePtr.toNativeInt pR.Pointer
        let mutable pcc = pc0
        for c in 0 .. cols - 1 do
            // wiki performs this loop backwards (should not really matter)
            let mutable prc = pcc + drR
            let mutable pr0 = pc0 + drR
            for r in c + 1 .. rows - 1 do 
                let vcc : float = NativeInt.read pcc // important since R.[c,c] changes
                let vrc : float = NativeInt.read prc 

                // if the dst-element is not already zero then make it zero
                if not (tiny eps vrc) then

                    // find givens rotation
                    let rho = float (sign vcc) * sqrt (vcc * vcc + vrc * vrc)
                    let cos = vcc / rho
                    let sin = vrc / rho
                    
                    let mutable p0 = pcc
                    let mutable p1 = prc 
                    // adjust affected elements
                    for ci in c .. cols - 1 do
                        let A = NativeInt.read<float> p0
                        let B = NativeInt.read<float> p1
                        
                        NativeInt.write p0 ( cos * A + sin * B )
                        NativeInt.write p1 (-sin * A + cos * B )
                        
                        p0 <- p0 + dcR
                        p1 <- p1 + dcR

                        
                    // adjust the resulting Q matrix
                    applyGivensMat pQ c r cos sin
                
                pr0 <- pr0 + drR
                prc <- prc + drR
            
            pc0 <- pc0 + drR
            pcc <- pcc + drR + dcR

    let svdBidiagonal (U : float[,]) (B : float[,]) (Vt : float[,]) =
        let U = Array2D.copy U
        let B = Array2D.copy B
        let Vt = Array2D.copy Vt

        let n = B.GetLength(0)
        let m = B.GetLength(1)
        
        let anorm =
            let mutable maxNorm = 0.0
            for r in 0..n-1 do
                maxNorm <- max maxNorm (abs B.[r,r] + (if r = 0 then 0.0 else abs B.[r-1,r]))
            maxNorm

        let mutable c = 0.0
        let mutable s = 0.0

        let mutable rvl0 = 0.0

        let inline rvl i =
            if i = 0 then rvl0
            else B.[i-1,i]
                
        let inline setrvl i v =
            if i = 0 then rvl0 <- v
            else B.[i-1,i] <- v

        let mutable f = 0.0
        let mutable g = 0.0
        let mutable h = 0.0
        
        let mutable x = 0.0
        let mutable y = 0.0
        let mutable z = 0.0

        for k in n - 1 .. -1 .. 0 do 
            let mutable conv = false
            let mutable iterations = 0
            while not conv && iterations <= 30 do
                inc &iterations
                let mutable flag = true
                let mutable nm = 0
                let mutable l = k
                let mutable testing = true
                while testing && l >= 0 do
                    nm <- l - 1
                    if abs (rvl l) + anorm = anorm then
                        flag <- false
                        testing <- false
                    elif abs B.[nm,nm] + anorm = anorm then
                        testing <- false
                    else
                        dec &l

                    
                if flag then
                    c <- 0.0
                    s <- 1.0
                    for i in l .. k do
                        f <- s * rvl i
                        if abs f + anorm <> anorm then
                            g <- B.[i,i]
                            h <- Fun.Pythag(f, g)
                            B.[i,i] <- h
                            h <- 1.0 / h
                            c <- g * h
                            s <- -f * h

                            for j in 0 .. m - 1 do
                                let y = U.[j, nm];
                                let z = U.[j, i];
                                U.[j, nm] <- (y * c + z * s);
                                U.[j, i] <- (z * c - y * s);
                            
                z <- B.[k,k] 
                if l = k then
                    // TODO!!!!!
                    //if z < 0.0 then // make singular value nonnegative
                    //{
                    //    w[k] = -z;
                    //    for (j = 0; j < n; j++)
                    //        v[k, j] = -v[k, j];
                    //}
                    
                    conv <- true
                else
                    printfn "..."
                    print B

                    if (iterations >= 30) then
                        failwith "no convergence after 30 iterations"

                    // shift from bottom 2 x 2 minor
                    x <- B.[l,l];
                    nm <- k - 1;
                    y <- B.[nm, nm];

                    g <- rvl nm;
                    h <- rvl k;
                    f <- ((y - z) * (y + z) + (g - h) * (g + h)) / (2.0 * h * y)
                    g <- Fun.Pythag(f, 1.0)
                    f <- ((x - z) * (x + z) + h * ((y / (f + (if (f >= 0.0) then abs(g) else -abs(g)))) - h)) / x

                    // next QR transformation
                    c <- 1.0
                    s <- 1.0

                    for j in l .. nm do
                        let i = j + 1
                        g <- rvl i
                        y <- B.[i,i]
                        h <- s * g
                        g <- c * g
                        z <- Fun.Pythag(f, h)
                        setrvl j z
                        c <- f / z
                        s <- h / z
                        f <- x * c + g * s
                        g <- g * c - x * s
                        h <- y * s
                        y <- y * c
                        for jj in 0 .. n - 1 do
                            let x = Vt.[j, jj]
                            let z = Vt.[i, jj]
                            Vt.[j, jj] <- x * c + z * s
                            Vt.[i, jj] <- z * c - x * s

                        z <- Fun.Pythag(f, h)
                        B.[j,j] <- z

                        if z <> 0.0 then
                            z <- 1.0 / z
                            c <- f * z
                            s <- h * z

                        f <- (c * g) + (s * y)
                        x <- (c * y) - (s * g)

                        for jj in 0 .. m-1 do
                            let y = U.[jj, j]
                            let z = U.[jj, i]
                            U.[jj, j] <- y * c + z * s
                            U.[jj, i] <- z * c - y * s
                    
                    setrvl l 0.0
                    setrvl k f
                    B.[k,k] <- x
        
        let inline swap i0 i1 =
            applyGivens U i0 i1 0.0 1.0
            Fun.Swap(&B.[i0,i0], &B.[i1,i1])
            applyGivensTransposed Vt i0 i1 0.0 1.0


        let mutable values = MapExt.empty
        let cmp = System.Func<_,_,_>(fun (_,l) (_,r) -> compare r l) 
        let heap = System.Collections.Generic.List<int * float>()
        for i in 0 .. n - 1 do
            let v = abs B.[i,i]
            values <- 
                MapExt.alter v (fun o ->
                    let o = defaultArg o []
                    Some (i :: o)
                ) values
            //heap.HeapEnqueue(cmp, (i, abs B.[i,i]))



        for i0 in 0..n-1 do
            let biggestIdx =
                let (key, indices) = MapExt.tryItem (values.Count - 1) values |> Option.get
                match indices with
                    | [i0] -> 
                        values <- MapExt.remove key values
                        i0
                    | i0 :: r ->
                        values <- MapExt.add key r values
                        i0
                    | _ ->
                        failwith ""
                
            if biggestIdx <> i0 then
                let v0 = B.[i0, i0]
                swap i0 biggestIdx
               
                values <- 
                    MapExt.alter v0 (fun o ->
                        let o = Option.defaultValue [] o
                        o |> List.map (fun ii -> if ii = i0 then biggestIdx else ii) |> Some
                    ) values

    
        for i0 in 0..n-2 do
            if B.[i0,i0] < 0.0 then
                let i1 = n-1
                B.[i0,i0] <- -B.[i0,i0]
                B.[i1,i1] <- -B.[i1,i1]
                //applyGivens U i0 i1 -1.0 0.0
                applyGivensTransposed Vt i0 i1 -1.0 0.0
                

        U, B, Vt


    let decomposeNative32 (eps : float32) (pQ : NativeMatrix<float32>) (pR : NativeMatrix<float32>) =
        let rows = int pR.SY
        let cols = int pR.SX

        // pQ <- identity
        pQ.SetByCoord (fun (v : V2i) -> if v.X = v.Y then 1.0f else 0.0f)
        
        let sa = nativeint sizeof<float32>
        let drR = nativeint pR.DY * sa
        let dcR = nativeint pR.DX * sa

        let mutable pc0 = NativePtr.toNativeInt pR.Pointer
        let mutable pcc = pc0
        for c in 0 .. cols - 1 do
            // wiki performs this loop backwards (should not really matter)
            let mutable prc = pcc + drR
            let mutable pr0 = pc0 + drR
            for r in c + 1 .. rows - 1 do 
                let vcc = NativeInt.read<float32> pcc // important since R.[c,c] changes
                let vrc = NativeInt.read<float32> prc 

                // if the dst-element is not already zero then make it zero
                if not (tiny eps vrc) then

                    // find givens rotation
                    let rho = float32 (sign vcc) * sqrt (vcc * vcc + vrc * vrc)
                    let cos = vcc / rho
                    let sin = vrc / rho
                    
                    let mutable p0 = pcc
                    let mutable p1 = prc 
                    // adjust affected elements
                    for ci in c .. cols - 1 do
                        let A = NativeInt.read<float32> p0
                        let B = NativeInt.read<float32> p1
                        
                        NativeInt.write p0 ( cos * A + sin * B )
                        NativeInt.write p1 (-sin * A + cos * B )

                        p0 <- p0 + dcR
                        p1 <- p1 + dcR

                        
                    // adjust the resulting Q matrix
                    applyGivensMat32 pQ c r cos sin
                
                pr0 <- pr0 + drR
                prc <- prc + drR
            
            pc0 <- pc0 + drR
            pcc <- pcc + drR + dcR

    let decomposeMat (eps : float) (mat : Matrix<float>) =
        let rows = int mat.SY
        let cols = int mat.SX

        let R = mat.Copy()
        let Q = Matrix<float>(int64 rows, int64 rows)
        
        NativeMatrix.using R (fun pR ->
            NativeMatrix.using Q (fun pQ ->
                decomposeNative eps pQ pR
                Q, R
            )
        )
[<AbstractClass; Sealed; Extension>]
type QRExtensions private() =
    [<Extension>]
    static member QRFactorize(this : M33d, ?eps : float) =
        let eps = defaultArg eps 1E-20
        let mutable Q = M33d()
        let mutable R = this

        let pQ = 
            NativeMatrix<float>(
                NativePtr.cast &&Q,
                MatrixInfo(
                    0L,
                    V2l(3, 3),
                    V2l(1, 3)
                )
            )
        let pR = 
            NativeMatrix<float>(
                NativePtr.cast &&R,
                MatrixInfo(
                    0L,
                    V2l(3, 3),
                    V2l(1, 3)
                )
            )
        QR.decomposeNative eps pQ pR
        Q, R
        
    [<Extension>]
    static member QRFactorize(this : M44d, ?eps : float) =
        let eps = defaultArg eps 1E-20
        let mutable Q = M44d()
        let mutable R = this

        let pQ = 
            NativeMatrix<float>(
                NativePtr.cast &&Q,
                MatrixInfo(
                    0L,
                    V2l(4, 4),
                    V2l(1, 4)
                )
            )
        let pR = 
            NativeMatrix<float>(
                NativePtr.cast &&R,
                MatrixInfo(
                    0L,
                    V2l(4, 4),
                    V2l(1, 4)
                )
            )
        QR.decomposeNative eps pQ pR
        Q, R
        
    [<Extension>]
    static member QRFactorize(this : M34d, ?eps : float) =
        let eps = defaultArg eps 1E-20
        let mutable Q = M33d()
        let mutable R = this

        let pQ = 
            NativeMatrix<float>(
                NativePtr.cast &&Q,
                MatrixInfo(
                    0L,
                    V2l(3, 3),
                    V2l(1, 3)
                )
            )
        let pR = 
            NativeMatrix<float>(
                NativePtr.cast &&R,
                MatrixInfo(
                    0L,
                    V2l(4, 3),
                    V2l(1, 4)
                )
            )
        QR.decomposeNative eps pQ pR
        Q, R
        
    [<Extension>]
    static member QRFactorize(this : M33f, ?eps : float32) =
        let eps = defaultArg eps 1E-10f
        let mutable Q = M33f()
        let mutable R = this

        let pQ = 
            NativeMatrix<float32>(
                NativePtr.cast &&Q,
                MatrixInfo(
                    0L,
                    V2l(3, 3),
                    V2l(1, 3)
                )
            )
        let pR = 
            NativeMatrix<float32>(
                NativePtr.cast &&R,
                MatrixInfo(
                    0L,
                    V2l(3, 3),
                    V2l(1, 3)
                )
            )
        QR.decomposeNative32 eps pQ pR
        Q, R
        
    [<Extension>]
    static member QRFactorize(this : M44f, ?eps : float32) =
        let eps = defaultArg eps 1E-10f
        let mutable Q = M44f()
        let mutable R = this

        let pQ = 
            NativeMatrix<float32>(
                NativePtr.cast &&Q,
                MatrixInfo(
                    0L,
                    V2l(4, 4),
                    V2l(1, 4)
                )
            )
        let pR = 
            NativeMatrix<float32>(
                NativePtr.cast &&R,
                MatrixInfo(
                    0L,
                    V2l(4, 4),
                    V2l(1, 4)
                )
            )
        QR.decomposeNative32 eps pQ pR
        Q, R
          
    [<Extension>]
    static member QRFactorize(this : M34f, ?eps : float32) =
        let eps = defaultArg eps 1E-10f
        let mutable Q = M33f()
        let mutable R = this

        let pQ = 
            NativeMatrix<float32>(
                NativePtr.cast &&Q,
                MatrixInfo(
                    0L,
                    V2l(3, 3),
                    V2l(1, 3)
                )
            )
        let pR = 
            NativeMatrix<float32>(
                NativePtr.cast &&R,
                MatrixInfo(
                    0L,
                    V2l(4, 3),
                    V2l(1, 4)
                )
            )
        QR.decomposeNative32 eps pQ pR
        Q, R
        
module Matrix =
    open Aardvark.Base.MultimethodTest

    let toArray (m : Matrix<'a>) =
        Array2D.init (int m.SY) (int m.SX) (fun r c ->
            m.[c,r]
        )

    let ofArray (m : 'a[,]) =
        let r = m.GetLength(0)
        let c = m.GetLength(1)

        let mat = Matrix(int64 c, int64 r)
        mat.SetByCoord(fun (c : V2l) ->
            m.[int c.Y, int c.X]
        )

[<AutoOpen>]
module MatrixUtils =
    
    let tolerance = 1E-8

    module Array2D =
        let toSeq (a : 'a[,]) =
            seq {
                for i0 in 0 .. a.GetLength(0) - 1 do
                    for i1 in 0 .. a.GetLength(1) - 1 do
                        yield a.[i0, i1]
            }

    let applyGivens (mat : float[,]) (c : int) (r : int) (cos : float) (sin : float) =
        let cols = mat.GetLength(0)
        // adjust affected elements
        for ci in 0 .. cols - 1 do
            let A = mat.[ci, c]
            let B = mat.[ci, r]
            mat.[ci, c] <-  cos * A + sin * B
            mat.[ci, r] <- -sin * A + cos * B

    let printTable (sep : bool) (arr : string[,]) =
        
        let maxLength =
            arr |> Array2D.toSeq |> Seq.map (fun str -> str.Length) |> Seq.max

        let pad (str : string) =
            if str.Length < maxLength then
                let diff = maxLength - str.Length
                let left = diff / 2
                let right = diff - left
                System.String(' ', left) + str + System.String(' ', right)
            else
                str
            
        let totalLength = arr.GetLength(1) * (maxLength + 4) //+ (arr.[0].Length - 1) * 3
        
        let line = System.String('-', totalLength)
        if sep then printfn "%s" line

        for r in 0 .. arr.GetLength(0) - 1 do
            if sep then printf "|"
            for c in 0 .. arr.GetLength(1) - 1 do
                let e = arr.[r,c]
                if sep then printf " %s | " (pad e)
                else printf " %s " (pad e)
            printfn ""
                
        if sep then printfn "%s" line
        ()


    let print (m : float[,]) =
        m |> Array2D.map (sprintf "%.3f") |> printTable false



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

    let skip (r : int) (c : int) (A : 'a[,])=
        let rows = A.GetLength(0)
        let cols = A.GetLength(1)
        Array2D.init (rows - 1) (cols - 1) (fun ri ci ->
            let ri = if ri >= r then ri + 1 else ri
            let ci = if ci >= c then ci + 1 else ci
            A.[ri,ci]
        )    

    let rec determinant (A : float[,]) =
        let rows = A.GetLength(0)
        let cols = A.GetLength(1)
        if rows <> cols then failwith "not quadratic"
        let size = rows
        match size with
            | 1 -> 
                A.[0,0]
            | 2 -> 
                A.[0,0] * A.[1,1] - A.[1,0] * A.[0,1]

            | 3 ->
                A.[0,0] * A.[1,1] * A.[2,2] +
                A.[0,1] * A.[1,2] * A.[2,0] +
                A.[0,2] * A.[1,0] * A.[2,1] -
                A.[0,2] * A.[1,1] * A.[2,0] -
                A.[0,1] * A.[1,0] * A.[2,2] -
                A.[0,0] * A.[1,2] * A.[2,1]

            | _ ->
                let mutable sum = 0.0
                let mutable s = 1.0
                for i in 0 .. size - 1 do
                    let d = determinant (skip 0 i A)
                    sum <- sum + s * A.[0,i] * d
                    s <- -s
                sum


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
        let Q, R = QR.decomposeMat eps (Matrix.ofArray mat)
        let Q = Matrix.toArray Q
        let R = Matrix.toArray R

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
                let Q, R = QR.decomposeMat 1.0E-20 (Matrix.ofArray mat)
                let Q = Matrix.toArray Q
                let R = Matrix.toArray R


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
        
    open Aardvark.VRVis
    let bidiag() =
        let rows = 6
        let cols = 6
        
        let m = 
            Array2D.init rows cols (fun r c ->
                rand.NextDouble() * 20.0 - 10.0
            )
            
        let svd = (Matrix.ofArray m).SVD()

        let Ua = Matrix.toArray svd.U
        let Wa = svd.W.Array
        let Va = Matrix.toArray svd.V

        let (U,B,Vt) = QR.bidiagonalize 1E-20 m

        let test = mul U (mul B Vt)
        printfn "Bidiag-test: %A" <| distanceMinMaxAvg test m
        printfn "Bidiag"
        print B

        let (U,B,Vt) = QR.svdBidiagonal U B Vt
        let test = mul U (mul B Vt)
        printfn "%A" <| distanceMinMaxAvg test m
        
        //printfn "raute"
        //printfn "Ua"
        //print Ua
        //printfn "Ba"
        //printfn "%A" Wa
        //printfn "Va"
        //print Va

        printfn "fsharp"
        printfn "U"
        print U
        printfn "B"
        print B
        printfn "Vt"
        print Vt
        printfn "det(U) = %A" (determinant U)
        printfn "det(V) = %A" (determinant Vt)
        ()
        //printfn "Vt"
        //print Vt
        