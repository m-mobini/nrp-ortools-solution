// Copyright 2010-2021 Google LLC
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

using System;
using System.Collections.Generic;
using System.Linq;
using Google.OrTools.Sat;

/// <summary>
/// Creates a shift scheduling problem and solves it
/// </summary>
public class RotationAutomation
{

    public static int NumEmployees { get; set; }
    public static int NumWeeks { get; set; }
    public static string[] Shifts { get; set; }
    public static int NumDays { get; set; }
    public static int NumShifts { get; set; }
    public static string SolverStringParameters { get; set; }
    public static (int Employee, int Shift, int Day)[] FixedAssignments { get; set; }
    public static (int Employee, int Shift, int Day, int Weight)[] Requests { get; set; }

    static void Main(string[] args)
    {
        SolveShiftScheduling();
    }

    private static void SetInitialParameters()
    {
        SolverStringParameters = " log_search_progress: true, max_time_in_seconds:30000, enumerate_all_solutions:false";
        NumEmployees = 21;
        NumWeeks = 21;
        NumDays = NumWeeks * 7;

        Shifts = new[] { "O", "d", "n" };
        NumShifts = Shifts.Length;

        // Fixed assignment: (employee, shift, day).
        // This fixes the first 2 days of the schedule.
        FixedAssignments = new (int Employee, int Shift, int Day)[] { };

        // Request: (employee, shift, day, weight)
        // A negative weight indicates that the employee desire this assignment.
        Requests = new (int Employee, int Shift, int Day,
                   int Weight)[] { };
    }

    static void SolveShiftScheduling()
    {
        SetInitialParameters();

        // Shift constraints on continuous sequence :
        //     (shift, hard_min, soft_min, min_penalty, soft_max, hard_max, max_penalty)
        var shiftConstraints =
            new(int Shift, int HardMin, int SoftMin, int MinPenalty, int SoftMax, int HardMax, int MaxPenalty)[] {
                // Min two and max 5 consecutive days of off-shift, this is a hard constraint.
                (0, 2, 2, 0, 5, 5, 0),
                // min and max day shifts.
                (1, 1, 1, 0, 4, 4, 0),
                // min and max night shifts.
                (2, 1, 1, 0, 2, 2, 0),
            };


        // Weekly sum constraints on shifts days:
        //     (shift, hardMin, softMin, minPenalty,
        // softMax, hardMax, maxPenalty)
        var weeklySumConstraints =
            new(int Shift, int HardMin, int SoftMin, int MinPenalty, int SoftMax, int HardMax, int MaxPenalty)[] {
                // Constraints on rests per week.
                (0, 2, 2, 0, 5, 5, 0),
            };

        // Penalized transitions:
        //     (previous_shift, next_shift, penalty (0 means forbidden))
        var penalizedTransitions = new(int PreviousShift, int NextShift, int Penalty)[] {
            // Night to day is forbidden.
            (2, 1, 0),
            // Off to Night is forbidden.
            (0, 2, 0),
        };

        // daily demands for work shifts (day, night) for each day
        // of the week starting on Monday.
        var dailyCoverDemands = new[]
        {
            new[] { 7, 3 }, // Friday
            new[] { 3, 0 }, // Saturday
            new[] { 8, 3 }, // Sunday
            new[] { 8, 3 }, // Monday
            new[] { 8, 3 }, // Tuesday
            new[] { 8, 3 }, // Wednesday
            new[] { 8, 3 }, // Thursday
        };
        // Penalty for exceeding the cover constraint per shift type.
        var excessCoverPenalties = new[] { 1, 1 }; //TODO use this variable instead of the hardcoded values 

        
        var model = new CpModel();

        var work = new IntVar[NumEmployees, NumShifts, NumDays];

        foreach (int e in Range(NumEmployees))
        foreach (int s in Range(NumShifts))
        foreach (int d in Range(NumDays))
            work[e, s, d] = model.NewBoolVar($"work_{e}_{s}_{d}");

        // Linear terms of the objective in a minimization context.
        var objIntVars = new List<IntVar>();
        var objIntCoeffs = new List<int>();
        var objBoolVars = new List<IntVar>();
        var objBoolCoeffs = new List<int>();

        // Exactly one shift per day.
        foreach (var e in Range(NumEmployees))
        foreach (var d in Range(NumDays))
        {
            var temp = new IntVar[NumShifts];
            foreach (int s in Range(NumShifts)) temp[s] = work[e, s, d];
            model.Add(LinearExpr.Sum(temp) == 1);
        }

        // Consecutive Shift constraints
        foreach (var constraint in shiftConstraints)
        foreach (int e in Range(NumEmployees))
        {
            var works = new IntVar[NumDays];
            foreach (int d in Range(NumDays)) works[d] = work[e, constraint.Shift, d];

            // Forbid sequences that are too short.
            foreach (var length in Range(1, constraint.HardMin))
            foreach (var start in Range(works.Length + 1))
            {
                var sequence = new List<ILiteral>();
                sequence.Add(start == 0 
                    ? works[works.GetLength(0) - 1] 
                    : works[start - 1]);
                sequence.AddRange(Range(length)
                    .Select(i => start + i < works.Length
                        ? works[start + i].Not()
                        : works[start + i - works.Length].Not()));
                sequence.Add(start + length < works.Length
                    ? works[start + length]
                    : works[start + length - works.Length]);
                model.AddBoolOr(sequence.ToArray());
            }
            // Forbid any sequence of true variables with length hardMax + 1
            foreach (var start in Range(works.GetLength(0)))
            {
                var temp = Range(start, start + constraint.HardMax + 1)
                    .Select(d => d < NumDays 
                        ? works[d].Not() 
                        : works[d - NumDays].Not()).ToList();
                model.AddBoolOr(temp);
            }
        }
        // Consecutive on-shifts constraints
        var consecutiveOnShiftConstraints =
            new (int HardMin, int SoftMin, int MinPenalty, int SoftMax, int HardMax, int MaxPenalty)[] {
                // Min two and max 4 consecutive days of on-shift, this is a hard constraint.
                (2, 2, 0, 4, 4, 0),
            };
        AddConsecutiveOnShiftConstraints(work, consecutiveOnShiftConstraints, model);

        // Total Sum constraints
        var totalSumConstraints =
            new (int Shift, int HardMin, int SoftMin, int MinPenalty, int SoftMax, int HardMax, int MaxPenalty)[] {
                (0, 79, 79, 0, 79, 79, 0),
                (1, 50, 50, 0, 50, 50, 0),
                (2, 18, 18, 0, 18, 18, 0),
            };
        foreach (var constraint in totalSumConstraints)
        foreach (int e in Range(NumEmployees))
        {
            var works = new IntVar[NumDays];

            foreach (int d in Range(NumDays)) works[d] = work[e, constraint.Shift, d];

            var (variables, coeffs) = AddSoftSumConstraint(
                model, works, constraint.HardMin, constraint.SoftMin, constraint.MinPenalty, constraint.SoftMax,
                constraint.HardMax, constraint.MaxPenalty,
                $"weekly_sum_constraint(employee {e}, shift {constraint.Shift}");

            objBoolVars.AddRange(variables);
            objBoolCoeffs.AddRange(coeffs);
        }

        // Weekly sum constraints //TODO is this set of constraints needed?
        foreach (var constraint in weeklySumConstraints)
        foreach (int e in Range(NumEmployees))
        foreach (int w in Range(NumWeeks))
        {
            var works = new IntVar[7];

            foreach (int d in Range(7)) 
                works[d] = work[e, constraint.Shift, d + w * 7];

            var (variables, coeffs) = AddSoftSumConstraint(
                model, works, constraint.HardMin, constraint.SoftMin, constraint.MinPenalty, constraint.SoftMax,
                constraint.HardMax, constraint.MaxPenalty,
                $"weekly_sum_constraint(employee {e}, shift {constraint.Shift}, week {w}");

            objBoolVars.AddRange(variables);
            objBoolCoeffs.AddRange(coeffs);
        }

        // Penalized transitions
        foreach (var penalizedTransition in penalizedTransitions)
        foreach (int e in Range(NumEmployees))
        foreach (int d in Range(NumDays))
        {
            var transition = new List<ILiteral>();
            transition.Add(work[e, penalizedTransition.PreviousShift, d].Not());
            transition.Add(work[e, penalizedTransition.NextShift,
                d + 1 < NumDays ? d + 1 : d + 1 - NumDays].Not());

            if (penalizedTransition.Penalty == 0)
                model.AddBoolOr(transition);
            else
            {
                var transVar = model.NewBoolVar($"transition (employee {e}, day={d}");
                transition.Add(transVar);
                model.AddBoolOr(transition);
                objBoolVars.Add(transVar);
                objBoolCoeffs.Add(penalizedTransition.Penalty);
            }
        }

        // Daily cover constraints
        foreach (int s in Range(1, NumShifts))
        foreach (int w in Range(NumWeeks))
        foreach (int d in Range(7))
        {
            var works = new IntVar[NumEmployees];
            foreach (int e in Range(NumEmployees)) works[e] = work[e, s, w * 7 + d];
            var minDemand = dailyCoverDemands[d][s - 1];
            var (variables, coeffs) = AddSoftSumConstraint(
                model, works, 0, minDemand, 1000, minDemand,
                NumEmployees, 1,
                $"shortage_sum_constraint(week {w}, day {d}");
            objBoolVars.AddRange(variables);
            objBoolCoeffs.AddRange(coeffs);
        }

        // Fixed assignments.
        foreach (var (e, s, d) in FixedAssignments)
        {
        }

        // Employee requests
        foreach (var (e, s, d, w) in Requests)
        {
            objBoolVars.Add(work[e, s, d]);
            objBoolCoeffs.Add(w);
        }
        // Objective
        var objBoolSum = LinearExpr.ScalProd(objBoolVars, objBoolCoeffs);
        var objIntSum = LinearExpr.ScalProd(objIntVars, objIntCoeffs);

        model.Minimize(objBoolSum + objIntSum);

        // Solve model
        var solver = new CpSolver();
        solver.StringParameters = SolverStringParameters;
        SolutionPrinter cb = new SolutionPrinter(work);

        var status = solver.Solve(model, cb);
        Console.WriteLine($"Number of solutions found: {cb.SolutionCount()}");

        // Print solution
        PrintSolutionToConsole(status, solver,
                               work,   objBoolVars,  objBoolCoeffs, objIntVars,
                               objIntCoeffs);
    }
    /// <summary>
    /// Adds constraints that enforces minimum and maximum consecutive On-shifts.
    /// </summary>
    /// <param name="work">Array of IntVar that are indexed as [employee, shift, day]</param>
    /// <param name="consecutiveOnShiftConstraints"></param>
    /// <param name="model"></param>
    private static void AddConsecutiveOnShiftConstraints(IntVar[,,] work,
                                                         (int HardMin, int SoftMin, int
                                                             MinPenalty, int SoftMax, int
                                                             HardMax, int MaxPenalty)[]
                                                             consecutiveOnShiftConstraints,
                                                         CpModel model)
    {
        for (int nId = 0; nId < NumEmployees; nId++)
        {
            var works = new IntVar[NumDays, NumShifts];
            for (int d = 0; d < NumDays; d++)
            for (int s = 0; s < NumShifts; s++) // skips the off shift 
                works[d, s] = work[nId, s, d];

            var costCoefficients = new List<int>();
            // Forbid sequences that are too short. For each on-shift:
            // get the surrounding negated span of length smaller than the hardMin, wrap it with the neighboring cells. 
            // add boolOr constraints.
            foreach (var length in Range(1, consecutiveOnShiftConstraints[0].HardMin))
            foreach (var start in Range(works.GetLength(0) - length + 1))
            foreach (var shift in Range(Shifts.Length))
            {
                if (IsOff(Shifts[shift]))
                    continue;
                var sequence = new List<ILiteral>();
                // start can be zero if HardMin is zero. 
                if (start == 0)
                    for (int s = 1; s < NumShifts; s++)
                        sequence.Add(works[works.GetLength(0) - 1, s]);
                else
                    for (int s = 1; s < NumShifts; s++)
                        sequence.Add(works[start - 1, s]);

                sequence.AddRange(Range(length)
                    .Select(i => start + i < works.GetLength(0)
                        ? works[start + i, shift].Not()
                        : works[start + i - works.GetLength(0), shift].Not()));

                if (start + length < works.GetLength(0))
                    for (int s = 1; s < NumShifts; s++)
                        sequence.Add(works[start + length, s]);
                else if (start + length >= works.GetLength(0))
                    for (int s = 1; s < NumShifts; s++)
                        sequence.Add(works[start + length - works.GetLength(0), s]);

                var r = sequence.ToArray();
                model.AddBoolOr(r);
            }
        }

        // forbid maximum length of on-shifts 
        for (int nId = 0; nId < NumEmployees; nId++)
        {
            var works = new IntVar[NumDays];
            for (int d = 0; d < NumDays; d++) works[d] = work[nId, 0, d];

            // forbid any sequence of true variables with length hardMax +1
            foreach (var start in Range(works.Length))
            {
                var temp = new List<ILiteral>();

                foreach (var d in Range(start,
                                        start + consecutiveOnShiftConstraints[0].HardMax + 1))
                    temp.Add(d >= NumDays ? works[d - NumDays] : works[d]);

                model.AddBoolOr(temp);
            }
        }
    }

    private static bool IsOff(string shift)
    {
        if (shift == "O")
            return true;
        return false;
    }

    private static void PrintSolutionToConsole(CpSolverStatus status, 
                                               CpSolver       solver,        IntVar[,,]   work,
                                               List<IntVar> objBoolVars,
                                               List<int>      objBoolCoeffs, List<IntVar> objIntVars,
                                               List<int>      objIntCoeffs)
    {
        if (status == CpSolverStatus.Optimal || status == CpSolverStatus.Feasible)
        {
            Console.WriteLine();
            var header = "          ";
            for (int w = 0; w < NumWeeks; w++) header += "M T W T F S S ";

            Console.WriteLine(header);

            foreach (int e in Range(NumEmployees))
            {
                var schedule = "";
                foreach (int d in Range(NumDays))
                {
                    foreach (int s in Range(NumShifts))
                    {
                        if (solver.BooleanValue(work[e, s, d]))
                        {
                            schedule += Shifts[s] + " ";
                        }
                    }
                }

                Console.WriteLine($"worker {e}: {schedule}");
            }

            Console.WriteLine();
            Console.WriteLine("Penalties:");

            foreach (var (i, var) in objBoolVars.Select((x, i) => (i, x)))
                if (solver.BooleanValue(var))
                {
                    var penalty = objBoolCoeffs[i];
                    if (penalty > 0)
                        Console.WriteLine($"  {var.Name()} violated, penalty={penalty}");
                    else
                        Console.WriteLine($"  {var.Name()} fulfilled, gain={-penalty}");
                }

            foreach (var (i, var) in objIntVars.Select((x, i) => (i, x)))
                if (solver.Value(var) > 0)
                {
                    Console.WriteLine(
                        $"  {var.Name()} violated by {solver.Value(var)}, linear penalty={objIntCoeffs[i]}");
                }

            Console.WriteLine();
            Console.WriteLine("Statistics");
            Console.WriteLine($"  - status          : {status}");
            Console.WriteLine($"  - conflicts       : {solver.NumConflicts()}");
            Console.WriteLine($"  - branches        : {solver.NumBranches()}");
            Console.WriteLine($"  - wall time       : {solver.WallTime()}"); 
        }
    }

    

    /// <summary>
    /// Filters an isolated sub-sequence of variables assigned to True.
    /// Extract the span of Boolean variables[start, start + length), negate them,
    /// and if there is variables to the left / right of this span, surround the
    /// span by them in non negated form.
    /// </summary>
    /// <param name="works">A list of variables to extract the span from.</param>
    /// <param name="start">The start to the span.</param>
    /// <param name="length">The length of the span.</param>
    /// <returns>An array of variables which conjunction will be false if the
    /// sub-list is assigned to True, and correctly bounded by variables assigned
    /// to False, or by the start or end of works.</returns>
    static ILiteral[] NegatedBoundedSpan(IntVar[] works, int start, int length)
    {
        var sequence = new List<ILiteral>();

        if (start > 0)
            sequence.Add(works[start - 1]);

        foreach (var i in Range(length))
            sequence.Add(works[start + i].Not());

        if (start + length < works.Length)
            sequence.Add(works[start + length]);

        return sequence.ToArray();
    }

    /// <summary>
    /// Sequence constraint on true variables with soft and hard bounds.
    /// This constraint look at every maximal contiguous sequence of variables
    /// assigned to true. If forbids sequence of length &lt; hardMin or &gt;
    /// hardMax. Then it creates penalty terms if the length is &lt; softMin or
    /// &gt; softMax.
    /// </summary>
    /// <param name="model">The sequence constraint is built on this
    /// model.</param> <param name="works">A list of Boolean variables.</param>
    /// <param name="hardMin">Any sequence of true variables must have a length of
    /// at least hardMin.</param> <param name="softMin">Any sequence should have a
    /// length of at least softMin, or a linear penalty on the delta will be added
    /// to the objective.</param> <param name="minCost">The coefficient of the
    /// linear penalty if the length is less than softMin.</param> <param
    /// name="softMax">Any sequence should have a length of at most softMax, or a
    /// linear penalty on the delta will be added to the objective.</param> <param
    /// name="hardMax">Any sequence of true variables must have a length of at
    /// most hardMax.</param> <param name="maxCost">The coefficient of the linear
    /// penalty if the length is more than softMax.</param> <param name="prefix">A
    /// base name for penalty literals.</param> <returns>A tuple (costLiterals,
    /// costCoefficients) containing the different penalties created by the
    /// sequence constraint.</returns>
    static (IntVar[] costLiterals, int[] costCoefficients)
        AddSoftSequenceConstraint(CpModel model, IntVar[] works, int hardMin, int softMin, int minCost, int softMax,
                                  int hardMax, int maxCost, string prefix)
    {
        var costLiterals = new List<IntVar>();
        var costCoefficients = new List<int>();

        // Forbid sequences that are too short.
        foreach (var length in Range(1, hardMin))
        {
            foreach (var start in Range(works.Length - length + 1))
            {
                model.AddBoolOr(NegatedBoundedSpan(works, start, length));
            }
        }

        // Penalize sequences that are below the soft limit.

        //if (minCost > 0)
        //{
        //    foreach (var length in Range(hardMin, softMin))
        //    {
        //        foreach (var start in Range(works.Length - length + 1))
        //        {
        //            var span = NegatedBoundedSpan(works, start, length).ToList();
        //            var name = $": under_span(start={start}, length={length})";
        //            var lit = model.NewBoolVar(prefix + name);
        //            span.Add(lit);
        //            model.AddBoolOr(span);
        //            costLiterals.Add(lit);
        //            // We filter exactly the sequence with a short length.
        //            // The penalty is proportional to the delta with softMin.
        //            costCoefficients.Add(minCost * (softMin - length));
        //        }
        //    }
        //}

        // Penalize sequences that are above the soft limit.
        //if (maxCost > 0)
        //{
        //    foreach (var length in Range(softMax + 1, hardMax + 1))
        //    {
        //        foreach (var start in Range(works.Length - length + 1))
        //        {
        //            var span = NegatedBoundedSpan(works, start, length).ToList();
        //            var name = $": over_span(start={start}, length={length})";
        //            var lit = model.NewBoolVar(prefix + name);
        //            span.Add(lit);
        //            model.AddBoolOr(span);
        //            costLiterals.Add(lit);
        //            // Cost paid is max_cost * excess length.
        //            costCoefficients.Add(maxCost * (length - softMax));
        //        }
        //    }
        //}

        // Just forbid any sequence of true variables with length hardMax + 1
        foreach (var start in Range(works.Length))
        {
            var temp = new List<ILiteral>();

            foreach (var d in Range(start, start + hardMax + 1))
            {
                if (d < NumDays)
                    temp.Add(works[d].Not());
                else if (d >= NumDays)
                    temp.Add(works[d - NumDays].Not());
            }
            model.AddBoolOr(temp);
        }

        return (costLiterals.ToArray(), costCoefficients.ToArray());
    }

    /// <summary>
    /// Sum constraint with soft and hard bounds.
    /// This constraint counts the variables assigned to true from works.
    /// If forbids sum &lt; hardMin or &gt; hardMax.
    /// Then it creates penalty terms if the sum is &lt; softMin or &gt; softMax.
    /// </summary>
    /// <param name="model">The sequence constraint is built on this
    /// model.</param> <param name="works">A list of Boolean variables.</param>
    /// <param name="hardMin">Any sequence of true variables must have a length of
    /// at least hardMin.</param> <param name="softMin">Any sequence should have a
    /// length of at least softMin, or a linear penalty on the delta will be added
    /// to the objective.</param> <param name="minCost">The coefficient of the
    /// linear penalty if the length is less than softMin.</param> <param
    /// name="softMax">Any sequence should have a length of at most softMax, or a
    /// linear penalty on the delta will be added to the objective.</param> <param
    /// name="hardMax">Any sequence of true variables must have a length of at
    /// most hardMax.</param> <param name="maxCost">The coefficient of the linear
    /// penalty if the length is more than softMax.</param> <param name="prefix">A
    /// base name for penalty literals.</param> <returns>A tuple (costVariables,
    /// costCoefficients) containing the different penalties created by the
    /// sequence constraint.</returns>
    static (IntVar[] costVariables, int[] costCoefficients)
        AddSoftSumConstraint(CpModel model, IntVar[] works, int hardMin, int softMin, int minCost, int softMax,
                             int hardMax, int maxCost, string prefix)
    {
        var costVariables = new List<IntVar>();
        var costCoefficients = new List<int>();
        var sumVar = model.NewIntVar(hardMin, hardMax, "");
        // This adds the hard constraints on the sum.
        model.Add(sumVar == LinearExpr.Sum(works));

        var zero = model.NewConstant(0);

        // Penalize sums below the soft_min target.

        if (softMin > hardMin && minCost > 0)
        {
            var delta = model.NewIntVar(-works.Length, works.Length, "");
            model.Add(delta == (softMin - sumVar));
            var excess = model.NewIntVar(0, works.Length, prefix + ": under_sum");
            model.AddMaxEquality(excess, new[] { delta, zero });
            costVariables.Add(excess);
            costCoefficients.Add(minCost);
        }

        // Penalize sums above the soft_max target.
        if (softMax < hardMax && maxCost > 0)
        {
            var delta = model.NewIntVar(-works.Length, works.Length, "");
            model.Add(delta == sumVar - softMax);
            var excess = model.NewIntVar(0, works.Length, prefix + ": over_sum");
            model.AddMaxEquality(excess, new[] { delta, zero });
            costVariables.Add(excess);
            costCoefficients.Add(maxCost);
        }

        return (costVariables.ToArray(), costCoefficients.ToArray());
    }

    /// <summary>
    /// C# equivalent of Python range (start, stop)
    /// </summary>
    /// <param name="start">The inclusive start.</param>
    /// <param name="stop">The exclusive stop.</param>
    /// <returns>A sequence of integers.</returns>
    static IEnumerable<int> Range(int start, int stop)
    {
        foreach (var i in Enumerable.Range(start, stop - start))
            yield return i;
    }

    /// <summary>
    /// C# equivalent of Python range (stop)
    /// </summary>
    /// <param name="stop">The exclusive stop.</param>
    /// <returns>A sequence of integers.</returns>
    static IEnumerable<int> Range(int stop)
    {
        return Range(0, stop);
    }
}

public class SolutionPrinter : CpSolverSolutionCallback
{
    public SolutionPrinter(IntVar[,,] variables)
    {
        _variables = variables;
    }

    public override void OnSolutionCallback()
    {
        {
            Console.WriteLine("Solution #{0}: time = {1:F2} s", _solutionCount, WallTime());
            foreach (IntVar v in _variables)
            {
                //Console.WriteLine("  {0} = {1}", v.ShortString(), Value(v));
            }
            _solutionCount++;
        }
    }

    public int SolutionCount()
    {
        return _solutionCount;
    }

    private int _solutionCount;
    private IntVar[,,] _variables;
}