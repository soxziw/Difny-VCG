method min2D(a: array<array<int>>)
  returns (r: int)
  requires a.Length > 0 // 1D length
  requires forall i :: 0 <= i < a.Length ==> a[i].Length > 0 // 2D length
  ensures forall ii, jj :: 0 <= ii < a.Length && 0 <= jj < a[ii].Length ==> r <= a[ii][jj] // minimum of whole 2D array
{
  var min := a[0][0];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length // i in loop
    invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < a[ii].Length ==> min <= a[ii][jj] // minimum of prev rows
  {
    for j := 0 to a[i].Length
      invariant 0 <= j <= a[i].Length // j in loop
      invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < a[ii].Length ==> min <= a[ii][jj] //  minimum of prev rows
      invariant forall jj :: 0 <= jj < j ==> min <= a[i][jj] //  minimum of prev columns of cur row
    {
      if a[i][j] < min {
        min := a[i][j];
      }
    }
  }
  return min;
}