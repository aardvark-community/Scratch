using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

// code copied from https://github.com/mathnet/mathnet-numerics/blob/1ff8db9b6037781e80e1d981438e8cdf0ba87076/src/Numerics/Providers/LinearAlgebra/Managed/ManagedLinearAlgebraProvider.Double.cs
// to be removed 

namespace RautenSharp
{
    public static class Class2
    {
        
        public class NonConvergenceException : Exception
        {
            public NonConvergenceException() : base()
            {
            }

            public NonConvergenceException(string message) : base(message)
            {
            }

            public NonConvergenceException(string message, Exception innerException) : base(message, innerException)
            {
            }
#if !NETSTANDARD1_3
            protected NonConvergenceException(System.Runtime.Serialization.SerializationInfo info, System.Runtime.Serialization.StreamingContext context)
                : base(info, context)
            {
            }
#endif
        }

        public const int SizeOfDouble = sizeof(double);
        
        private const int DoubleWidth = 53;
        
        public static readonly double DoublePrecision = Math.Pow(2, -DoubleWidth);

        public static int Magnitude(this double value)
        {
            // Can't do this with zero because the 10-log of zero doesn't exist.
            if (value.Equals(0.0))
            {
                return 0;
            }

            // Note that we need the absolute value of the input because Log10 doesn't
            // work for negative numbers (obviously).
            double magnitude = Math.Log10(Math.Abs(value));
            var truncated = (int)Math.Truncate(magnitude);

            // To get the right number we need to know if the value is negative or positive
            // truncating a positive number will always give use the correct magnitude
            // truncating a negative number will give us a magnitude that is off by 1 (unless integer)
            return magnitude < 0d && truncated != magnitude
                ? truncated - 1
                : truncated;
        }

        
        public static bool AlmostEqualNormRelative(this double a, double b, double diff, int decimalPlaces)
        {
            if (decimalPlaces < 0)
            {
                // Can't have a negative number of decimal places
                throw new ArgumentOutOfRangeException("decimalPlaces");
            }

            // If A or B are a NAN, return false. NANs are equal to nothing,
            // not even themselves.
            if (double.IsNaN(a) || double.IsNaN(b))
            {
                return false;
            }

            // If A or B are infinity (positive or negative) then
            // only return true if they are exactly equal to each other -
            // that is, if they are both infinities of the same sign.
            if (double.IsInfinity(a) || double.IsInfinity(b))
            {
                return a == b;
            }

            // If both numbers are equal, get out now. This should remove the possibility of both numbers being zero
            // and any problems associated with that.
            if (a.Equals(b))
            {
                return true;
            }

            // If one is almost zero, fall back to absolute equality
            if (Math.Abs(a) < DoublePrecision || Math.Abs(b) < DoublePrecision)
            {
                // The values are equal if the difference between the two numbers is smaller than
                // 10^(-numberOfDecimalPlaces). We divide by two so that we have half the range
                // on each side of the numbers, e.g. if decimalPlaces == 2,
                // then 0.01 will equal between 0.005 and 0.015, but not 0.02 and not 0.00
                return Math.Abs(diff) < Math.Pow(10, -decimalPlaces) / 2d;
            }

            // If the magnitudes of the two numbers are equal to within one magnitude the numbers could potentially be equal
            int magnitudeOfFirst = Magnitude(a);
            int magnitudeOfSecond = Magnitude(b);
            int magnitudeOfMax = Math.Max(magnitudeOfFirst, magnitudeOfSecond);
            if (magnitudeOfMax > (Math.Min(magnitudeOfFirst, magnitudeOfSecond) + 1))
            {
                return false;
            }

            // The values are equal if the difference between the two numbers is smaller than
            // 10^(-numberOfDecimalPlaces). We divide by two so that we have half the range
            // on each side of the numbers, e.g. if decimalPlaces == 2,
            // then 0.01 will equal between 0.00995 and 0.01005, but not 0.0015 and not 0.0095
            return Math.Abs(diff) < Math.Pow(10, magnitudeOfMax - decimalPlaces) / 2d;
        }

        public static bool AlmostEqualRelative(this double a, double b, int decimalPlaces)
        {
            return AlmostEqualNormRelative(a, b, a - b, decimalPlaces);
        }

        /// <summary>
        /// Given the Cartesian coordinates (da, db) of a point p, these function return the parameters da, db, c, and s
        /// associated with the Givens rotation that zeros the y-coordinate of the point.
        /// </summary>
        /// <param name="da">Provides the x-coordinate of the point p. On exit contains the parameter r associated with the Givens rotation</param>
        /// <param name="db">Provides the y-coordinate of the point p. On exit contains the parameter z associated with the Givens rotation</param>
        /// <param name="c">Contains the parameter c associated with the Givens rotation</param>
        /// <param name="s">Contains the parameter s associated with the Givens rotation</param>
        /// <remarks>This is equivalent to the DROTG LAPACK routine.</remarks>
        static void Drotg(ref double da, ref double db, out double c, out double s)
        {
            double r, z;

            var roe = db;
            var absda = Math.Abs(da);
            var absdb = Math.Abs(db);
            if (absda > absdb)
            {
                roe = da;
            }

            var scale = absda + absdb;
            if (scale == 0.0)
            {
                c = 1.0;
                s = 0.0;
                r = 0.0;
                z = 0.0;
            }
            else
            {
                var sda = da/scale;
                var sdb = db/scale;
                r = scale*Math.Sqrt((sda*sda) + (sdb*sdb));
                if (roe < 0.0)
                {
                    r = -r;
                }

                c = da/r;
                s = db/r;
                z = 1.0;
                if (absda > absdb)
                {
                    z = s;
                }

                if (absdb >= absda && c != 0.0)
                {
                    z = 1.0/c;
                }
            }

            da = r;
            db = z;
        }


        /// <summary>
        /// Computes the singular value decomposition of A.
        /// </summary>
        /// <param name="computeVectors">Compute the singular U and VT vectors or not.</param>
        /// <param name="a">On entry, the M by N matrix to decompose. On exit, A may be overwritten.</param>
        /// <param name="rowsA">The number of rows in the A matrix.</param>
        /// <param name="columnsA">The number of columns in the A matrix.</param>
        /// <param name="s">The singular values of A in ascending value.</param>
        /// <param name="u">If <paramref name="computeVectors"/> is <c>true</c>, on exit U contains the left
        /// singular vectors.</param>
        /// <param name="vt">If <paramref name="computeVectors"/> is <c>true</c>, on exit VT contains the transposed
        /// right singular vectors.</param>
        /// <remarks>This is equivalent to the GESVD LAPACK routine.</remarks>
        public static void SingularValueDecomposition(bool computeU, bool computeV, double[] a, int rowsA, int columnsA, double[] s, double[] u, double[] vt)
        {
            var work = new double[rowsA];

            const int maxiter = 1000;

            var e = new double[columnsA];
            var v = vt != null ? new double[vt.Length] : null;
            var stemp = new double[Math.Min(rowsA + 1, columnsA)];

            int i, j, l, lp1;

            double t;

            var ncu = rowsA;

            // Reduce matrix to bidiagonal form, storing the diagonal elements
            // in "s" and the super-diagonal elements in "e".
            var nct = Math.Min(rowsA - 1, columnsA);
            var nrt = Math.Max(0, Math.Min(columnsA - 2, rowsA));
            var lu = Math.Max(nct, nrt);

            for (l = 0; l < lu; l++)
            {
                lp1 = l + 1;
                if (l < nct)
                {
                    // Compute the transformation for the l-th column and
                    // place the l-th diagonal in vector s[l].
                    var sum = 0.0;
                    for (var i1 = l; i1 < rowsA; i1++)
                    {
                        sum += a[(l*rowsA) + i1]*a[(l*rowsA) + i1];
                    }

                    stemp[l] = Math.Sqrt(sum);

                    if (stemp[l] != 0.0)
                    {
                        if (a[(l*rowsA) + l] != 0.0)
                        {
                            stemp[l] = Math.Abs(stemp[l])*(a[(l*rowsA) + l]/Math.Abs(a[(l*rowsA) + l]));
                        }

                        // A part of column "l" of Matrix A from row "l" to end multiply by 1.0 / s[l]
                        for (i = l; i < rowsA; i++)
                        {
                            a[(l*rowsA) + i] = a[(l*rowsA) + i]*(1.0/stemp[l]);
                        }

                        a[(l*rowsA) + l] = 1.0 + a[(l*rowsA) + l];
                    }

                    stemp[l] = -stemp[l];
                }

                for (j = lp1; j < columnsA; j++)
                {
                    if (l < nct)
                    {
                        if (stemp[l] != 0.0)
                        {
                            // Apply the transformation.
                            t = 0.0;
                            for (i = l; i < rowsA; i++)
                            {
                                t += a[(j*rowsA) + i]*a[(l*rowsA) + i];
                            }

                            t = -t/a[(l*rowsA) + l];

                            for (var ii = l; ii < rowsA; ii++)
                            {
                                a[(j*rowsA) + ii] += t*a[(l*rowsA) + ii];
                            }
                        }
                    }

                    // Place the l-th row of matrix into "e" for the
                    // subsequent calculation of the row transformation.
                    e[j] = a[(j*rowsA) + l];
                }

                if (computeU && l < nct)
                {
                    // Place the transformation in "u" for subsequent back multiplication.
                    for (i = l; i < rowsA; i++)
                    {
                        u[(l*rowsA) + i] = a[(l*rowsA) + i];
                    }
                }

                if (l >= nrt)
                {
                    continue;
                }

                // Compute the l-th row transformation and place the l-th super-diagonal in e(l).
                var enorm = 0.0;
                for (i = lp1; i < e.Length; i++)
                {
                    enorm += e[i]*e[i];
                }

                e[l] = Math.Sqrt(enorm);
                if (e[l] != 0.0)
                {
                    if (e[lp1] != 0.0)
                    {
                        e[l] = Math.Abs(e[l])*(e[lp1]/Math.Abs(e[lp1]));
                    }

                    // Scale vector "e" from "lp1" by 1.0 / e[l]
                    for (i = lp1; i < e.Length; i++)
                    {
                        e[i] = e[i]*(1.0/e[l]);
                    }

                    e[lp1] = 1.0 + e[lp1];
                }

                e[l] = -e[l];

                if (lp1 < rowsA && e[l] != 0.0)
                {
                    // Apply the transformation.
                    for (i = lp1; i < rowsA; i++)
                    {
                        work[i] = 0.0;
                    }

                    for (j = lp1; j < columnsA; j++)
                    {
                        for (var ii = lp1; ii < rowsA; ii++)
                        {
                            work[ii] += e[j]*a[(j*rowsA) + ii];
                        }
                    }

                    for (j = lp1; j < columnsA; j++)
                    {
                        var ww = -e[j]/e[lp1];
                        for (var ii = lp1; ii < rowsA; ii++)
                        {
                            a[(j*rowsA) + ii] += ww*work[ii];
                        }
                    }
                }

                if (!computeV)
                {
                    continue;
                }

                // Place the transformation in v for subsequent back multiplication.
                for (i = lp1; i < columnsA; i++)
                {
                    v[(l*columnsA) + i] = e[i];
                }
            }

            // Set up the final bidiagonal matrix or order m.
            var m = Math.Min(columnsA, rowsA + 1);
            var nctp1 = nct + 1;
            var nrtp1 = nrt + 1;
            if (nct < columnsA)
            {
                stemp[nctp1 - 1] = a[((nctp1 - 1)*rowsA) + (nctp1 - 1)];
            }

            if (rowsA < m)
            {
                stemp[m - 1] = 0.0;
            }

            if (nrtp1 < m)
            {
                e[nrtp1 - 1] = a[((m - 1)*rowsA) + (nrtp1 - 1)];
            }

            e[m - 1] = 0.0;

            // If required, generate "u".
            if (computeU)
            {
                for (j = nctp1 - 1; j < ncu; j++)
                {
                    for (i = 0; i < rowsA; i++)
                    {
                        u[(j*rowsA) + i] = 0.0;
                    }

                    u[(j*rowsA) + j] = 1.0;
                }

                for (l = nct - 1; l >= 0; l--)
                {
                    if (stemp[l] != 0.0)
                    {
                        for (j = l + 1; j < ncu; j++)
                        {
                            t = 0.0;
                            for (i = l; i < rowsA; i++)
                            {
                                t += u[(j*rowsA) + i]*u[(l*rowsA) + i];
                            }

                            t = -t/u[(l*rowsA) + l];

                            for (var ii = l; ii < rowsA; ii++)
                            {
                                u[(j*rowsA) + ii] += t*u[(l*rowsA) + ii];
                            }
                        }

                        // A part of column "l" of matrix A from row "l" to end multiply by -1.0
                        for (i = l; i < rowsA; i++)
                        {
                            u[(l*rowsA) + i] = u[(l*rowsA) + i]*-1.0;
                        }

                        u[(l*rowsA) + l] = 1.0 + u[(l*rowsA) + l];
                        for (i = 0; i < l; i++)
                        {
                            u[(l*rowsA) + i] = 0.0;
                        }
                    }
                    else
                    {
                        for (i = 0; i < rowsA; i++)
                        {
                            u[(l*rowsA) + i] = 0.0;
                        }

                        u[(l*rowsA) + l] = 1.0;
                    }
                }
            }

            // If it is required, generate v.
            if (computeV)
            {
                for (l = columnsA - 1; l >= 0; l--)
                {
                    lp1 = l + 1;
                    if (l < nrt)
                    {
                        if (e[l] != 0.0)
                        {
                            for (j = lp1; j < columnsA; j++)
                            {
                                t = 0.0;
                                for (i = lp1; i < columnsA; i++)
                                {
                                    t += v[(j*columnsA) + i]*v[(l*columnsA) + i];
                                }

                                t = -t/v[(l*columnsA) + lp1];
                                for (var ii = l; ii < columnsA; ii++)
                                {
                                    v[(j*columnsA) + ii] += t*v[(l*columnsA) + ii];
                                }
                            }
                        }
                    }

                    for (i = 0; i < columnsA; i++)
                    {
                        v[(l*columnsA) + i] = 0.0;
                    }

                    v[(l*columnsA) + l] = 1.0;
                }
            }

            // Transform "s" and "e" so that they are double
            for (i = 0; i < m; i++)
            {
                double r;
                if (stemp[i] != 0.0)
                {
                    t = stemp[i];
                    r = stemp[i]/t;
                    stemp[i] = t;
                    if (i < m - 1)
                    {
                        e[i] = e[i]/r;
                    }

                    if (computeU)
                    {
                        // A part of column "i" of matrix U from row 0 to end multiply by r
                        for (j = 0; j < rowsA; j++)
                        {
                            u[(i*rowsA) + j] = u[(i*rowsA) + j]*r;
                        }
                    }
                }

                // Exit
                if (i == m - 1)
                {
                    break;
                }

                if (e[i] == 0.0)
                {
                    continue;
                }

                t = e[i];
                r = t/e[i];
                e[i] = t;
                stemp[i + 1] = stemp[i + 1]*r;
                if (!computeV)
                {
                    continue;
                }

                // A part of column "i+1" of matrix VT from row 0 to end multiply by r
                for (j = 0; j < columnsA; j++)
                {
                    v[((i + 1)*columnsA) + j] = v[((i + 1)*columnsA) + j]*r;
                }
            }

            // Main iteration loop for the singular values.
            var mn = m;
            var iter = 0;

            while (m > 0)
            {
                // Quit if all the singular values have been found.
                // If too many iterations have been performed throw exception.
                if (iter >= maxiter)
                {
                    throw new NonConvergenceException();
                }

                // This section of the program inspects for negligible elements in the s and e arrays,
                // on completion the variables case and l are set as follows:
                // case = 1: if mS[m] and e[l-1] are negligible and l < m
                // case = 2: if mS[l] is negligible and l < m
                // case = 3: if e[l-1] is negligible, l < m, and mS[l, ..., mS[m] are not negligible (qr step).
                // case = 4: if e[m-1] is negligible (convergence).
                double ztest;
                double test;
                for (l = m - 2; l >= 0; l--)
                {
                    test = Math.Abs(stemp[l]) + Math.Abs(stemp[l + 1]);
                    ztest = test + Math.Abs(e[l]);
                    if (ztest.AlmostEqualRelative(test, 15))
                    {
                        e[l] = 0.0;
                        break;
                    }
                }

                int kase;
                if (l == m - 2)
                {
                    kase = 4;
                }
                else
                {
                    int ls;
                    for (ls = m - 1; ls > l; ls--)
                    {
                        test = 0.0;
                        if (ls != m - 1)
                        {
                            test = test + Math.Abs(e[ls]);
                        }

                        if (ls != l + 1)
                        {
                            test = test + Math.Abs(e[ls - 1]);
                        }

                        ztest = test + Math.Abs(stemp[ls]);
                        if (ztest.AlmostEqualRelative(test, 15))
                        {
                            stemp[ls] = 0.0;
                            break;
                        }
                    }

                    if (ls == l)
                    {
                        kase = 3;
                    }
                    else if (ls == m - 1)
                    {
                        kase = 1;
                    }
                    else
                    {
                        kase = 2;
                        l = ls;
                    }
                }

                l = l + 1;

                // Perform the task indicated by case.
                int k;
                double f;
                double cs;
                double sn;
                switch (kase)
                {
                        // Deflate negligible s[m].
                    case 1:
                        f = e[m - 2];
                        e[m - 2] = 0.0;
                        double t1;
                        for (var kk = l; kk < m - 1; kk++)
                        {
                            k = m - 2 - kk + l;
                            t1 = stemp[k];

                            Drotg(ref t1, ref f, out cs, out sn);
                            stemp[k] = t1;
                            if (k != l)
                            {
                                f = -sn*e[k - 1];
                                e[k - 1] = cs*e[k - 1];
                            }

                            if (computeV)
                            {
                                // Rotate
                                for (i = 0; i < columnsA; i++)
                                {
                                    var z = (cs*v[(k*columnsA) + i]) + (sn*v[((m - 1)*columnsA) + i]);
                                    v[((m - 1)*columnsA) + i] = (cs*v[((m - 1)*columnsA) + i]) - (sn*v[(k*columnsA) + i]);
                                    v[(k*columnsA) + i] = z;
                                }
                            }
                        }

                        break;

                        // Split at negligible s[l].
                    case 2:
                        f = e[l - 1];
                        e[l - 1] = 0.0;
                        for (k = l; k < m; k++)
                        {
                            t1 = stemp[k];
                            Drotg(ref t1, ref f, out cs, out sn);
                            stemp[k] = t1;
                            f = -sn*e[k];
                            e[k] = cs*e[k];
                            if (computeU)
                            {
                                // Rotate
                                for (i = 0; i < rowsA; i++)
                                {
                                    var z = (cs*u[(k*rowsA) + i]) + (sn*u[((l - 1)*rowsA) + i]);
                                    u[((l - 1)*rowsA) + i] = (cs*u[((l - 1)*rowsA) + i]) - (sn*u[(k*rowsA) + i]);
                                    u[(k*rowsA) + i] = z;
                                }
                            }
                        }

                        break;

                        // Perform one qr step.
                    case 3:

                        // calculate the shift.
                        var scale = 0.0;
                        scale = Math.Max(scale, Math.Abs(stemp[m - 1]));
                        scale = Math.Max(scale, Math.Abs(stemp[m - 2]));
                        scale = Math.Max(scale, Math.Abs(e[m - 2]));
                        scale = Math.Max(scale, Math.Abs(stemp[l]));
                        scale = Math.Max(scale, Math.Abs(e[l]));
                        var sm = stemp[m - 1]/scale;
                        var smm1 = stemp[m - 2]/scale;
                        var emm1 = e[m - 2]/scale;
                        var sl = stemp[l]/scale;
                        var el = e[l]/scale;
                        var b = (((smm1 + sm)*(smm1 - sm)) + (emm1*emm1))/2.0;
                        var c = (sm*emm1)*(sm*emm1);
                        var shift = 0.0;
                        if (b != 0.0 || c != 0.0)
                        {
                            shift = Math.Sqrt((b*b) + c);
                            if (b < 0.0)
                            {
                                shift = -shift;
                            }

                            shift = c/(b + shift);
                        }

                        f = ((sl + sm)*(sl - sm)) + shift;
                        var g = sl*el;

                        // Chase zeros
                        for (k = l; k < m - 1; k++)
                        {
                            Drotg(ref f, ref g, out cs, out sn);
                            if (k != l)
                            {
                                e[k - 1] = f;
                            }

                            f = (cs*stemp[k]) + (sn*e[k]);
                            e[k] = (cs*e[k]) - (sn*stemp[k]);
                            g = sn*stemp[k + 1];
                            stemp[k + 1] = cs*stemp[k + 1];
                            if (computeV)
                            {
                                for (i = 0; i < columnsA; i++)
                                {
                                    var z = (cs*v[(k*columnsA) + i]) + (sn*v[((k + 1)*columnsA) + i]);
                                    v[((k + 1)*columnsA) + i] = (cs*v[((k + 1)*columnsA) + i]) - (sn*v[(k*columnsA) + i]);
                                    v[(k*columnsA) + i] = z;
                                }
                            }

                            Drotg(ref f, ref g, out cs, out sn);
                            stemp[k] = f;
                            f = (cs*e[k]) + (sn*stemp[k + 1]);
                            stemp[k + 1] = -(sn*e[k]) + (cs*stemp[k + 1]);
                            g = sn*e[k + 1];
                            e[k + 1] = cs*e[k + 1];
                            if (computeU && k < rowsA)
                            {
                                for (i = 0; i < rowsA; i++)
                                {
                                    var z = (cs*u[(k*rowsA) + i]) + (sn*u[((k + 1)*rowsA) + i]);
                                    u[((k + 1)*rowsA) + i] = (cs*u[((k + 1)*rowsA) + i]) - (sn*u[(k*rowsA) + i]);
                                    u[(k*rowsA) + i] = z;
                                }
                            }
                        }

                        e[m - 2] = f;
                        iter = iter + 1;
                        break;

                        // Convergence
                    case 4:

                        // Make the singular value  positive
                        if (stemp[l] < 0.0)
                        {
                            stemp[l] = -stemp[l];
                            if (computeV)
                            {
                                // A part of column "l" of matrix VT from row 0 to end multiply by -1
                                for (i = 0; i < columnsA; i++)
                                {
                                    v[(l*columnsA) + i] = v[(l*columnsA) + i]*-1.0;
                                }
                            }
                        }

                        // Order the singular value.
                        while (l != mn - 1)
                        {
                            if (stemp[l] >= stemp[l + 1])
                            {
                                break;
                            }

                            t = stemp[l];
                            stemp[l] = stemp[l + 1];
                            stemp[l + 1] = t;
                            if (computeV && l < columnsA)
                            {
                                // Swap columns l, l + 1
                                for (i = 0; i < columnsA; i++)
                                {
                                    var z = v[(l*columnsA) + i];
                                    v[(l*columnsA) + i] = v[((l + 1)*columnsA) + i];
                                    v[((l + 1)*columnsA) + i] = z;
                                }
                            }

                            if (computeU && l < rowsA)
                            {
                                // Swap columns l, l + 1
                                for (i = 0; i < rowsA; i++)
                                {
                                    var z = u[(l*rowsA) + i];
                                    u[(l*rowsA) + i] = u[((l + 1)*rowsA) + i];
                                    u[((l + 1)*rowsA) + i] = z;
                                }
                            }

                            l = l + 1;
                        }

                        iter = 0;
                        m = m - 1;
                        break;
                }
            }

            if (computeV)
            {
                // Finally transpose "v" to get "vt" matrix
                for (i = 0; i < columnsA; i++)
                {
                    for (j = 0; j < columnsA; j++)
                    {
                        vt[(j*columnsA) + i] = v[(i*columnsA) + j];
                    }
                }
            }

            // Copy stemp to s with size adjustment. We are using ported copy of linpack's svd code and it uses
            // a singular vector of length rows+1 when rows < columns. The last element is not used and needs to be removed.
            // We should port lapack's svd routine to remove this problem.
            Buffer.BlockCopy(stemp, 0, s, 0, Math.Min(rowsA, columnsA)*SizeOfDouble);
        }


    }
}