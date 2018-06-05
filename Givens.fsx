#r @"netstandard.dll"
#load @".paket\load\main.group.fsx"
#r "SVD.dll"

open System.Runtime.CompilerServices
open Microsoft.FSharp.NativeInterop
open Aardvark.Base
open Aardvark.VRVis
open Aardvark.Base.Sorting
#nowarn "9"
#nowarn "51"
#nowarn "4321"

module NativeMatrix =
    open System.Runtime.InteropServices
    
    [<CompilerMessage("internal use only: use NativeMatrix.using instead", 4321, IsHidden = true)>]
    type Pinning private() =
        static member Using(m : M22d, f : NativeMatrix<float> -> 'r) =
            let mutable r = m
            let native =
                NativeMatrix<float>(
                    NativePtr.cast &&r,
                    MatrixInfo(
                        0L,
                        V2l(2,2),
                        V2l(1,2)
                    )
                )
            f native
                
        static member Using(m : M23d, f : NativeMatrix<float> -> 'r) =
            let mutable r = m
            let native =
                NativeMatrix<float>(
                    NativePtr.cast &&r,
                    MatrixInfo(
                        0L,
                        V2l(3,2),
                        V2l(1,3)
                    )
                )
            f native
                
        static member Using(m : M33d, f : NativeMatrix<float> -> 'r) =
            let mutable r = m
            let native =
                NativeMatrix<float>(
                    NativePtr.cast &&r,
                    MatrixInfo(
                        0L,
                        V2l(3,3),
                        V2l(1,3)
                    )
                )
            f native
            
        static member Using(m : M34d, f : NativeMatrix<float> -> 'r) =
            let mutable r = m
            let native =
                NativeMatrix<float>(
                    NativePtr.cast &&r,
                    MatrixInfo(
                        0L,
                        V2l(3,4),
                        V2l(1,4)
                    )
                )
            f native

        static member Using(m : M44d, f : NativeMatrix<float> -> 'r) =
            let mutable r = m
            let native =
                NativeMatrix<float>(
                    NativePtr.cast &&r,
                    MatrixInfo(
                        0L,
                        V2l(4,4),
                        V2l(1,4)
                    )
                )
            f native
            
        static member Using(m : float[,], f : NativeMatrix<float> -> 'r) =
            let gc = GCHandle.Alloc(m, GCHandleType.Pinned)
            try
                let rows = m.GetLength(0)
                let cols = m.GetLength(1)
                let native =
                    NativeMatrix<float>(
                        NativePtr.ofNativeInt (gc.AddrOfPinnedObject()),
                        MatrixInfo(
                            0L,
                            V2l(cols,rows),
                            V2l(1,cols)
                        )
                    )
                f native
            finally
                gc.Free()
                
        static member Using(m : Matrix<float>, f : NativeMatrix<float> -> 'r) =
            NativeMatrix.using m f

    [<CompilerMessage("internal use only: use NativeMatrix.using instead", 4321, IsHidden = true)>]
    let inline usingDummy< ^a, ^b, ^c, ^r when ^c : unmanaged and (^a or ^b) : (static member Using : ^a * (NativeMatrix< ^c > -> ^r) -> ^r) > (b : ^b) (a : ^a) (f : NativeMatrix< ^c > -> ^r) =
        ((^a or ^b) : (static member Using : ^a * (NativeMatrix< ^c > -> ^r) -> ^r) (a, f))

    let inline using a f =
        usingDummy Unchecked.defaultof<Pinning> a f

module QR =

    [<AutoOpen>]
    module private Helpers = 
        type NativeMatrix<'a when 'a : unmanaged> with
            member inline x.Transposed = NativeMatrix<'a>(x.Pointer, x.Info.Transposed)

        let inline sgn v = if v < 0.0 then -1.0 else 1.0

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
            let rows = mat.GetLength(0)
            // adjust affected elements
            for ri in 0 .. rows - 1 do
                let A = mat.[ri, c]
                let B = mat.[ri, r]
                mat.[ri, c] <-  cos * A + sin * B
                mat.[ri, r] <- -sin * A + cos * B

        let applyGivensTransposed (mat : float[,]) (c : int) (r : int) (cos : float) (sin : float) =
            let cols = mat.GetLength(1)
            // adjust affected elements
            for ci in 0 .. cols - 1 do
                let A = mat.[c, ci]
                let B = mat.[r, ci]
                mat.[c, ci] <-  cos * A + sin * B
                mat.[r, ci] <- -sin * A + cos * B
            
        let inline applyGivensMat (mat : NativeMatrix<float>) (c : int) (r : int) (cos : float) (sin : float) =
            let ptrQ = NativePtr.toNativeInt mat.Pointer
            let dcQ = nativeint sizeof<float> * nativeint mat.DX
            let drQ = nativeint sizeof<float> * nativeint mat.DY
            let rows = int mat.SY

            let mutable p0 = ptrQ + nativeint c * dcQ 
            let mutable p1 = ptrQ + nativeint r * dcQ      
            // adjust affected elements
            for _ in 0 .. rows - 1 do
                let A = NativeInt.read<float> p0 //mat.[ci, c]
                let B = NativeInt.read<float> p1 //mat.[ci, r]

                //mat.[ci, c] <-  cos * A + sin * B
                //mat.[ci, r] <- -sin * A + cos * B
                NativeInt.write p0 ( cos * A + sin * B )
                NativeInt.write p1 (-sin * A + cos * B )

                p0 <- p0 + drQ
                p1 <- p1 + drQ
                
        let inline applyGivensTransposedMat (mat : NativeMatrix<float>) (c : int) (r : int) (cos : float) (sin : float) =
            let ptrQ = NativePtr.toNativeInt mat.Pointer
            let dcQ = nativeint sizeof<float> * nativeint mat.DX
            let drQ = nativeint sizeof<float> * nativeint mat.DY
            let cols = int mat.SX

            let mutable p0 = ptrQ + nativeint c * drQ 
            let mutable p1 = ptrQ + nativeint r * drQ      
            // adjust affected elements
            for _ in 0 .. cols - 1 do
                let A = NativeInt.read<float> p0
                let B = NativeInt.read<float> p1
                NativeInt.write p0 ( cos * A + sin * B )
                NativeInt.write p1 (-sin * A + cos * B )

                p0 <- p0 + dcQ
                p1 <- p1 + dcQ


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

    /// creates a (in-place) decomposition B = U * B' * Vt where
    /// U and V a orthonormal rotations and B' is upper bidiagonal
    /// returns the "anorm" of the resulting B matrix
    let internal bidiagonalizeNative (U : NativeMatrix<float>) (B : NativeMatrix<float>) (Vt : NativeMatrix<float>) =
        let rows = int B.SY
        let cols = int B.SX

        // set u and v to identity
        U.SetByCoord(fun (v : V2i) -> if v.X = v.Y then 1.0 else 0.0)
        Vt.SetByCoord(fun (v : V2i) -> if v.X = v.Y then 1.0 else 0.0)

        let sa = nativeint sizeof<float>
        let pB = NativePtr.toNativeInt B.Pointer
        let dbr = nativeint B.DY * sa
        let dbc = nativeint B.DX * sa
        
        let mutable anorm = 0.0

        let mutable pii = pB
        for i in 0 .. cols - 1 do

            // make the subdiagonal column 0
            let mutable pi1i = pii + dbr
            for j in i + 1 .. rows - 1 do
                let vcc = NativeInt.read<float> pii     //B.[i,i]
                let vrc = NativeInt.read<float> pi1i    //B.[j,i]

                // if the dst-element is not already zero then make it zero
                if not (Fun.IsTiny vrc) then

                    // find givens rotation
                    let rho = sgn vcc * sqrt (vcc * vcc + vrc * vrc)
                    let cos = vcc / rho
                    let sin = vrc / rho
                    
                    // adjust affected elements
                    let mutable pr0 = pii 
                    let mutable pr1 = pi1i

                    // first iteration
                    let a = NativeInt.read<float> pr0 //B.[r0,ci]
                    let b = NativeInt.read<float> pr1 //B.[r1,ci]
                    NativeInt.write pr0 ( cos * a + sin * b )
                    NativeInt.write pr1 0.0
                    pr1 <- pr1 + dbc
                    pr0 <- pr0 + dbc

                    for _ in i+1 .. cols - 1 do
                        let a = NativeInt.read<float> pr0 //B.[r0,ci]
                        let b = NativeInt.read<float> pr1 //B.[r1,ci]
                        NativeInt.write pr0 ( cos * a + sin * b )
                        NativeInt.write pr1 (-sin * a + cos * b )
                        pr1 <- pr1 + dbc
                        pr0 <- pr0 + dbc

                    // adjust the resulting U matrix
                    applyGivensMat U i j cos sin
                    
                pi1i <- pi1i + dbr

                
            // step one to the right
            pii <- pii + dbc
            let i = i + 1
            let mutable pij = pii + dbc
            
            // make the 2nd superdiagonal row 0
            for j in i + 1 .. cols - 1 do
                let vcc = NativeInt.read<float> pii     //B.[i,i+1] // important since R.[c,c] changes
                let vrc = NativeInt.read<float> pij     //B.[i,j]

                // if the dst-element is not already zero then make it zero
                if not (Fun.IsTiny vrc) then

                    // find givens rotation
                    let rho = if vcc = 0.0 then abs vrc else sgn vcc * sqrt (vcc * vcc + vrc * vrc)
                    let sin = vrc / rho
                    let cos = vcc / rho
                    
                    // adjust affected elements
                    let mutable pc0 = pii
                    let mutable pc1 = pij
                    
                    // first iteration
                    let a = NativeInt.read<float> pc0 //B.[r0,ci]
                    let b = NativeInt.read<float> pc1 //B.[r1,ci]
                    NativeInt.write pc0 ( cos * a + sin * b )
                    NativeInt.write pc1 0.0
                    pc0 <- pc0 + dbr
                    pc1 <- pc1 + dbr


                    for _ in i .. rows - 1 do
                        let a = NativeInt.read<float> pc0 //B.[r0,ci]
                        let b = NativeInt.read<float> pc1 //B.[r1,ci]
                        NativeInt.write pc0 ( cos * a + sin * b )
                        NativeInt.write pc1 (-sin * a + cos * b )
                        pc0 <- pc0 + dbr
                        pc1 <- pc1 + dbr
                        
                    // adjust the resulting Vt matrix
                    applyGivensTransposedMat Vt i j cos sin
                    
                pij <- pij + dbc
                
            let normv =
                if i > 0 then 
                    // abs B.[i-1,i] + abs B.[i,i]
                    abs (NativeInt.read<float> (pii - dbc - dbr)) + abs (NativeInt.read<float> (pii - dbc))
                else 
                    // abs B.[i,i]
                    abs (NativeInt.read<float> (pii - dbc))

            anorm <- max anorm normv
            pii <- pii + dbr

        anorm

    let internal svdBidiagonalNative (anorm : float) (U : NativeMatrix<float>) (B : NativeMatrix<float>) (Vt : NativeMatrix<float>) : unit =
        let mutable c = 0.0
        let mutable s = 0.0
        let mutable rvl0 = 0.0

        let n = int B.SY
        let m = int B.SX

        let pB = NativePtr.toNativeInt B.Pointer
        let sa = nativeint sizeof<float>
        let dbc = nativeint B.DX * sa
        let dbr = nativeint B.DY * sa

        let pw = pB
        let dw = dbc + dbr

        let prvl = pB + dbc
        let drvl = dw
        
        let inline rvl i =
            if i = 0 then rvl0
            else NativeInt.read<float> (prvl + nativeint (i - 1) * drvl) //B.[i-1,i]
                
        let inline setrvl i v =
            if i = 0 then rvl0 <- v
            else NativeInt.write (prvl + nativeint (i - 1) * drvl) v //B.[i-1,i] <- v

        let inline w i =
            NativeInt.read<float> (pw + nativeint i * dw)
            
        let inline setw i (v : float) =
            NativeInt.write (pw + nativeint i * dw) v
             
        let mutable f = 0.0
        let mutable g = 0.0
        let mutable h = 0.0
        
        let mutable x = 0.0
        let mutable y = 0.0
        let mutable z = 0.0

        for k in m - 1 .. -1 .. 0 do 
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
                    elif abs (w nm) + anorm = anorm then
                        testing <- false
                    else
                        dec &l

                    
                if flag then
                    c <- 0.0
                    s <- 1.0
                    for i in l .. k do
                        f <- s * rvl i
                        if abs f + anorm <> anorm then
                            g <- w i //B.[i,i]
                            h <- Fun.Pythag(f, g)
                            setw i h // B.[i,i] <- h
                            h <- 1.0 / h
                            c <- g * h
                            s <- -f * h

                            applyGivensMat U nm i c s
                            
                z <- w k //B.[k,k] 
                if l = k then
                    conv <- true
                else

                    if (iterations >= 30) then
                        failwith "no convergence after 30 iterations"

                    // shift from bottom 2 x 2 minor
                    x <- w l //B.[l,l];
                    nm <- k - 1;
                    y <- w nm //B.[nm, nm];

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
                        y <- w i //B.[i,i]
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
                        applyGivensTransposedMat Vt j i c s

                        z <- Fun.Pythag(f, h)
                        setw j z //B.[j,j] <- z

                        if z <> 0.0 then
                            z <- 1.0 / z
                            c <- f * z
                            s <- h * z

                        f <- (c * g) + (s * y)
                        x <- (c * y) - (s * g)
                        applyGivensMat U j i c s
                    
                    setrvl l 0.0
                    setrvl k f
                    setw k x // B.[k,k] <- x
        
        let inline swap i0 i1 =
            applyGivensMat U i0 i1 0.0 1.0
            let t = w i0
            setw i0 (w i1)
            setw i1 t
            applyGivensTransposedMat Vt i0 i1 0.0 1.0
        let mutable values = MapExt.empty
        let cmp = System.Func<_,_,_>(fun (_,l) (_,r) -> compare r l) 
        let heap = System.Collections.Generic.List<int * float>()
        for i in 0 .. m - 1 do
            let v = abs (w i) //B.[i,i]
            values <- 
                MapExt.alter v (fun o ->
                    let o = defaultArg o []
                    Some (i :: o)
                ) values
                
        for i0 in 0..m-1 do
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
                let v0 = w i0 //B.[i0, i0]
                swap i0 biggestIdx
               
                values <- 
                    MapExt.alter v0 (fun o ->
                        let o = Option.defaultValue [] o
                        o |> List.map (fun ii -> if ii = i0 then biggestIdx else ii) |> Some
                    ) values

    
        for i0 in 0..m-2 do
            if w i0 < 0.0 then
                let i1 = m-1
                setw i0 (-w i0)
                setw i1 (-w i1)
                applyGivensTransposedMat Vt i0 i1 -1.0 0.0

    let svdNative (U : NativeMatrix<float>) (B : NativeMatrix<float>) (Vt : NativeMatrix<float>) =
        if B.SX <= B.SY then
            let anorm = bidiagonalizeNative U B Vt
            svdBidiagonalNative anorm U B Vt
        else
            // B = U * B' * Vt
            // Bt = V * Bt' * Ut
            let Ut = U.Transposed
            let V = Vt.Transposed
            let Bt = B.Transposed
            let anorm = bidiagonalizeNative V Bt Ut
            svdBidiagonalNative anorm V Bt Ut

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
                    let rho = sgn vcc * sqrt (vcc * vcc + vrc * vrc)
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
                    conv <- true
                else

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

module Matrix =
    open Aardvark.Base.MultimethodTest

    let toArray (m : Matrix<'a>) =
        Array2D.init (int m.SY) (int m.SX) (fun r c ->
            m.[c,r]
        )
        
    let toArrayT (m : Matrix<'a>) =
        Array2D.init (int m.SX) (int m.SY) (fun r c ->
            m.[r,c]
        )

    let ofArray (m : 'a[,]) =
        let r = m.GetLength(0)
        let c = m.GetLength(1)

        let mutable mat = Matrix(int64 c, int64 r)
        mat.SetByCoord(fun (c : V2l) ->
            m.[int c.Y, int c.X]
        ) |> ignore
        mat
    let ofArrayT (m : 'a[,]) =
        let r = m.GetLength(0)
        let c = m.GetLength(1)

        let mutable mat = Matrix(int64 r, int64 c)
        mat.SetByCoord(fun (c : V2l) ->
            m.[int c.X, int c.Y]
        ) |> ignore
        mat

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
    open System.Diagnostics

    let rand = System.Random()

    let random rows cols =
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

            fun r c ->
                Array2D.init r c (fun r c ->
                    if r = c then 0.0
                    else rand.NextDouble() * 20.0 - 10.0
                )

        |]

    let randomSpecial rows cols =
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
        
    let errorMetrics (square : bool) (name : string) (reconstruct : float[,] -> float[,]) (iter : int) =
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
                let rows, cols =
                    if square then 
                        let s = 1 + rand.Next(64)
                        s,s
                    else 
                        1 + rand.Next(64), 1 + rand.Next(64)
                let mat = if rand.NextDouble() > 0.1 then random rows cols else randomSpecial rows cols
                let test = reconstruct mat
                let (min, max, avg) = distanceMinMaxAvg mat test
                if max > 1E-5 then
                    printfn "bad:   { size = [%d, %d]; min = %e; max = %e; avg = %e }" (mat.GetLength(0)) (mat.GetLength(1)) min max avg
                    
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
                let pad (l : int) (c : char) (str : string) =
                    if str.Length < l then
                        let diff = l - str.Length
                        let left = diff / 2
                        let right = diff - left
                        System.String(c, left) + str + System.String(c, right)
                    else
                        str

                let maxLength =
                    arr |> Seq.collect (fun row ->
                        row |> Seq.map (fun str -> str.Length)
                    )
                    |> Seq.max

                let totalLength = arr.[0].Length * (maxLength + 4) //+ (arr.[0].Length - 1) * 3
                let line = pad totalLength '-' (" " + name + " ")
                printfn "%s" line

                for row in arr do
                    printf "|"
                    for e in row do
                        printf " %s | " (pad maxLength ' ' e)
                    printfn ""

                let line = System.String('-', totalLength)
                printfn "%s" line
                ()

            printTable table

    let metrics (iter : int) =
        let reconstructSVD (m : float[,]) =
            let S = Array2D.copy m
            let rows = m.GetLength(0)
            let cols = m.GetLength(1)
            let U = Array2D.zeroCreate rows rows
            let Vt = Array2D.zeroCreate cols cols
            NativeMatrix.using S (fun ps ->
                NativeMatrix.using U (fun pu ->
                    NativeMatrix.using Vt (fun pvt ->
                        QR.svdNative pu ps pvt
                    )
                )
            )

            mul U (mul S Vt)

        let reconstructQR (m : float[,]) =
            let R = Array2D.copy m
            let rows = m.GetLength(0)
            let Q = Array2D.zeroCreate rows rows

            NativeMatrix.using R (fun pr ->
                NativeMatrix.using Q (fun pq ->
                    QR.decomposeNative 1E-20 pq pr
                )
            )

            mul Q R

        let reconstructLU (m : float[,]) =
            try
                let s = m.GetLength(0)
                let m = Array2D.copy m
                let perm = m.LuFactorize()

                    
                let iperm = Array.zeroCreate perm.Length
                for i in 0 .. perm.Length-1 do
                    iperm.[perm.[i]] <- i

                let L =
                    Array2D.init s s (fun r c ->
                        let r = iperm.[r]
                        if c < r then
                            m.[r, c]
                        elif c = r then
                            1.0
                        else
                            0.0
                    )
                let R =
                    Array2D.init s s (fun r c ->
                        if c >= r then
                            m.[r, c]
                        else
                            0.0
                    )
                    
                mul L R
            with _ ->
                m
        

        let reconstructRautenSharp (m : float[,]) =
            let rows = m.GetLength(0)
            let cols = m.GetLength(1)
                
            let toCol (m : float[,]) =
                let rows = m.GetLength(0)
                let cols = m.GetLength(1)
                
                Array.init (rows * cols) (fun i ->
                    let r = i % rows
                    let c = i / rows
                    m.[r,c]
                )
            let ofCol (rows : int) (cols : int) (m : float[]) =
                Array2D.init rows cols (fun r c ->
                    m.[c * rows + r]
                )
                
            let u = Array.zeroCreate (rows * rows)
            let s = Array.zeroCreate (min rows cols)
            let vt = Array.zeroCreate (cols * cols)

            RautenSharp.Class2.SingularValueDecomposition(true, true, toCol m, m.GetLength(0), m.GetLength(1), s, u, vt)
        

            let U = ofCol rows rows u
            let Vt = ofCol cols cols vt
            let S =
                Array2D.init rows cols (fun r c ->
                    if r = c && r < s.Length then s.[r]
                    else 0.0
                )
            mul U (mul S Vt)


        errorMetrics false "QR" reconstructQR iter
        printfn ""
        errorMetrics false "SVD" reconstructSVD iter
        printfn ""
        errorMetrics true "LU" reconstructLU iter
        printfn ""
        errorMetrics true "RautenSharp" reconstructRautenSharp iter

    let perf () =
        let iter = 100000
        let rows = 16
        let cols = 16
        
        

        let m = 
            Array2D.init rows cols (fun r c ->
                rand.NextDouble() * 20.0 - 10.0
            )


        let luTime() =
            for i in 1 .. 5 do
                let B = Array2D.copy m
                let perm = B.LuFactorize()
                B.LuInverse(perm) |> ignore

            let sw = Stopwatch()
            for i in 1 .. iter do
                let B = Array2D.copy m
                sw.Start()
                let perm = B.LuFactorize()
                let inv = B.LuInverse(perm)
                sw.Stop()

            sw.MicroTime / iter
            
        let qrTime() =
            for i in 1 .. 5 do
                let B = Array2D.copy m
                B.QrInverse() |> ignore

            let sw = Stopwatch()
            for i in 1 .. iter do
                let B = Array2D.copy m
                sw.Start()
                let inv = B.QrInverse()
                sw.Stop()

            sw.MicroTime / iter
              
        let qrnTime() =
            let Q = Array2D.copy m
            NativeMatrix.using Q (fun q ->
                for i in 1 .. 5 do
                    let B = Array2D.copy m
                    NativeMatrix.using B (fun b ->
                        QR.decomposeNative 1E-20 q b |> ignore
                    )

                let sw = Stopwatch()
                for i in 1 .. iter do
                    let B = Array2D.copy m
                    sw.Start()
                    NativeMatrix.using B (fun b ->
                        QR.decomposeNative 1E-20 q b |> ignore
                    )
                    sw.Stop()

                sw.MicroTime / iter
            )

        let svdTime() =
            for i in 1 .. 5 do
                let B = Array2D.copy m
                let U = Array2D.zeroCreate rows rows
                let Vt = Array2D.zeroCreate cols cols
                
                NativeMatrix.using B (fun b ->
                    NativeMatrix.using U (fun u ->
                        NativeMatrix.using Vt (fun vt ->
                            QR.svdNative u b vt
                        )
                    )
                )
            let sw = Stopwatch()
            for i in 1 .. iter do
                let B = Array2D.copy m
                let U = Array2D.zeroCreate rows rows
                let Vt = Array2D.zeroCreate cols cols
                
                sw.Start()
                NativeMatrix.using B (fun b ->
                    NativeMatrix.using U (fun u ->
                        NativeMatrix.using Vt (fun vt ->
                            QR.svdNative u b vt
                        )
                    )
                )
                sw.Stop()

            sw.MicroTime / iter
            
        let svdoTime() =
            for i in 1 .. 5 do
                let B = Matrix.ofArray m
                let U = Array2D.zeroCreate rows rows
                let Vt = Array2D.zeroCreate cols cols
                
                B.SVD() |> ignore

            let sw = Stopwatch()
            for i in 1 .. iter do
                let B = Matrix.ofArray m
                
                sw.Start()
                B.SVD() |> ignore
                sw.Stop()

            sw.MicroTime / iter

        printf "LU:  "
        printfn "%A" (luTime())

        printf "QR:  "
        printfn "%A" (qrTime())
        
        printf "QR2: "
        printfn "%A" (qrnTime())

        printf "SVD: "
        printfn "%A" (svdTime())
        
        printf "SVO: "
        printfn "%A" (svdoTime())
        