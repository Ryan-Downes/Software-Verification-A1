// Everything in [l1, u1] is sorted non-decreasing
predicate sorted(l1: int, u1: int,a: array<int>)
    requires a != null &&  u1 < a.Length 
    reads a
{
    forall i,j::  (0 <= i && l1 <= i <= j <= u1) ==> a[i] <= a[j]
}

// Return smallest elem of a between left and right
function min(a : array<int>, left : int, right : int) : (minVal : int)
    requires a != null
    requires 0 <= left <= right < a.Length
    reads a
    decreases right - left
    ensures forall i:: left <= i <= right ==> a[i] >= minVal
    ensures a.Length == 0 || (exists i :: left <= i <= right && a[i] == minVal);
{
    if (left == right) then a[left]
    else if (a[left] <= min(a, left + 1, right)) then a[left]
    else min(a, left + 1, right)
}

// Return largest elem of a between left and right
function max(a : array<int>, left : int, right : int) : (maxVal : int)
    requires a != null
    requires 0 <= left <= right < a.Length
    reads a
    decreases right - left
    ensures forall i:: left <= i <= right ==> a[i] <= maxVal
    ensures a.Length == 0 || (exists i :: left <= i <= right && a[i] == maxVal);
{
    if (left == right) then a[left]
    else if (a[left] >= max(a, left + 1, right)) then a[left]
    else max(a, left + 1, right)
}

// lemma sortMaintained(a : array<int>, left : int, right : int)
//     requires a != null
//     requires 0 <= left < right < a.Length
//     requires sorted(left + 1, right, a)
//     requires a[left] <= a[right]
//     // we have: ensures max(a, left, right) == a[right]; // ==> sorted(left, right - 1, a)
//     ensures sorted(left, right - 1, a) ==> sorted(left, right, a);
// {


// }

// Sorts non-decreasing, then stoogeSort if atleast 3 elems left between L and R
// Swaps L & R if L > R
method stoogeSort(a : array<int>, left : int, right : int)
    requires a != null
    requires 0 <= left <= right < a.Length
    modifies a
    // Ensure elements outside left and right are untouched
    ensures forall i:: ((0 <= i < left) || (right < i < a.Length)) ==> a[i] == old(a[i])
    
    ensures a[left] <= old(a[left]) // a[left] only gets smaller
    ensures a[right] >= old(a[right]) // a[right] only gets larger

    //ensures multiset(a[..]) == old(multiset(a[..]))
    //ensures max(a, left, right) == old(max(a, left, right))
    //ensures min(a, left, right) == old(min(a, left, right))

    ensures sorted(left, right, a)
    decreases right - left;
{
    if (a[left] > a[right])
    {
        // swap a[left] and a[right]
        var tmp := a[left];
        a[left] := a[right];
        a[right] := tmp;
    }

    if (left + 1 >= right)
    {
        return;
    }
    stoogeSort(a, left, right - 1);
    assert sorted(left, right - 1, a);
    ghost var currMin := min(a, left, right - 1); // Min over all but last position
    assert a[left] == currMin;

    stoogeSort(a, left + 1, right);
    assert sorted(left + 1, right, a);
    ghost var finalMax := max(a, left, right); // Max over whole array
    assert a[right] == finalMax;

    ghost var oldRight := a[right];

    stoogeSort(a, left, right - 1);
    assert sorted(left, right - 1, a);
    //assert sorted(left + 1, right, a); // Doesnt hold because Dafny forgets a[right] is unchanged
    ghost var finalMin := min(a, left, right); // Min over whole array
    assert currMin >= finalMin;
    assert a[left] == finalMin;
    assert a[right] == finalMax;

    assert oldRight == a[right];

    assert finalMax == max(a, left, right); // TODO: Convince Dafny this value is unchanged.

    // Then generalize to k, with:
    // Let S1, S2, and S3 be the three parts of the array; we need to show that
    // sorted(S1 concat S2) AND sorted(S2 concat S3) ==> MAX(S1 join S2) <= MIN(S3)
}
