############################################################################
##
#W  bipartition.gi
#Y  Copyright (C) 2013-14                                James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

BindGlobal("BipartitionFamily", NewFamily("BipartitionFamily",
 IsBipartition, CanEasilySortElements, CanEasilySortElements));

BindGlobal("BipartitionType", NewType(BipartitionFamily,
 IsBipartition and IsComponentObjectRep and IsAttributeStoringRep));

#

InstallMethod(NaturalLeqBlockBijection, "for bipartitions", 
[IsBipartition, IsBipartition], 
function(f, g)
  local fblocks, gblocks, n, lookup, i;
  
  if not IsBlockBijection(f) or not IsBlockBijection(g) then 
    Error("usage: the arguments must be block bijections,");
    return;
  elif DegreeOfBipartition(f)<>DegreeOfBipartition(g) then 
    Error("usage: the arguments must be block bijections of equal degree,");
    return;
  elif NrBlocks(f)>NrBlocks(g) then 
    return false;
  fi;

  fblocks:=f!.blocks; gblocks:=g!.blocks;
  n:=DegreeOfBipartition(f);
  
  lookup:=[];
  for i in [1..n] do 
    if IsBound(lookup[gblocks[i]]) and lookup[gblocks[i]]<>fblocks[i] then 
      return false;
    else 
      lookup[gblocks[i]]:=fblocks[i];
    fi;
  od;
  for i in [n+1..2*n] do 
    if lookup[gblocks[i]]<>fblocks[i] then 
      return false;
    fi;
  od;
  return true;
end);

#

InstallMethod(NaturalLeqInverseSemigroup, "for two block bijections",
[IsBlockBijection, IsBlockBijection], NaturalLeqBlockBijection);

#

InstallOtherMethod(InverseMutable, "for a bipartition", [IsBipartition],
function(f)
  if IsBlockBijection(f) or IsPartialPermBipartition(f) then 
    return Star(f);
  else
    return fail;
  fi;
end);

#not a synonym since NrTransverseBlocks also applies to blocks
InstallMethod(NrTransverseBlocks, "for a bipartition", [IsBipartition], 
RankOfBipartition);

#

InstallMethod(NrRightBlocks, "for a bipartition", [IsBipartition], 
function(f) 
  return NrBlocks(f)-NrLeftBlocks(f)+NrTransverseBlocks(f);
end);

#operators

InstallMethod(\*, "for a bipartition and bipartition",
[IsBipartition, IsBipartition], 
function(a,b)
  local n, anr, fuse, fuseit, ablocks, bblocks, x, y, tab, cblocks, next, nrleft, c, i;
  
  n := DegreeOfBipartition(a);
  Assert(1,n = DegreeOfBipartition(b));
  anr := NrBlocks(a);
  
  fuse := [1..anr+NrBlocks(b)]; 
  
  fuseit := function(i) 
    while fuse[i] < i do 
      i := fuse[i]; 
    od; 
    return i; 
  end;
 
  ablocks:=a!.blocks;
  bblocks:=b!.blocks;

  for i in [1..n] do
    x := fuseit(ablocks[i+n]);
    y := fuseit(bblocks[i]+anr);
    if x <> y then
      if x < y then
        fuse[y] := x;
      else
        fuse[x] := y;
      fi;
    fi;
  od;
  
  tab:=0*fuse;    # A table for the old part numbers
  cblocks:=EmptyPlist(2*n);
  next:=0;
  
  for i in [1..n] do
    x := fuseit(ablocks[i]);
    if tab[x]=0 then
      next:=next+1;
      tab[x]:=next;
    fi;
    cblocks[i]:=tab[x];
  od;
  
  nrleft:=next;

  for i in [n+1..2*n] do
    x:=fuseit(bblocks[i]+anr);
    if tab[x]=0 then
      next:=next+1;
      tab[x]:=next;
    fi;
    cblocks[i]:=tab[x];
  od;
  
  c:=Objectify(BipartitionType, rec(blocks:=cblocks)); 

  SetDegreeOfBipartition(c, n);
  SetNrLeftBlocks(c, nrleft);
  SetNrBlocks(c, next);
  return c;
end);

#

InstallMethod(\*, "for a bipartition and a perm",
[IsBipartition, IsPerm],
function(f,g)
  return f*AsBipartition(g, DegreeOfBipartition(f));
end);

#

InstallMethod(\*, "for a perm and a bipartition",
[IsPerm, IsBipartition],
function(f,g)
  return AsBipartition(f, DegreeOfBipartition(g))*g;
end);

#

InstallMethod(\*, "for a bipartition and a transformation",
[IsBipartition, IsTransformation],
function(f,g)
  return f*AsBipartition(g, DegreeOfBipartition(f));
end);

#

InstallMethod(\*, "for a transformation and a bipartition",
[IsTransformation, IsBipartition],
function(f,g)
  return AsBipartition(f, DegreeOfBipartition(g))*g;
end);

#

InstallMethod(\*, "for a bipartition and a partial perm",
[IsBipartition, IsPartialPerm],
function(f,g)
  return f*AsBipartition(g, DegreeOfBipartition(f));
end);

#

InstallMethod(\*, "for a partial perm and a bipartition",
[IsPartialPerm, IsBipartition],
function(f,g)
  return AsBipartition(f, DegreeOfBipartition(g))*g;
end);

#

InstallMethod(\<, "for a bipartition and bipartition", 
[IsBipartition, IsBipartition],
function(f, g)
  return f!.blocks<g!.blocks;
end);

#

InstallMethod(\=, "for a bipartition and bipartition", 
[IsBipartition, IsBipartition],
function(f, g)
  return f!.blocks=g!.blocks;
end);

#

InstallMethod(\^, "for a bipartition and permutation",
[IsBipartition, IsPerm],
function(f, p)
  return p^-1*f*p;
end);

# LambdaPerm

InstallGlobalFunction(PermLeftQuoBipartitionNC,
function(f, g)
  local n, nr, fblocks, gblocks, p, tab, nrblocks, i;

  n:=DegreeOfBipartition(f);
  fblocks:=f!.blocks;
  gblocks:=g!.blocks;
  p:=[1..n];

  #figure out which blocks of f correspond to which blocks of the right blocks
  #of f 
  nr:=0;
  tab:=EmptyPlist(2*n);
  for i in [n+1..2*n] do 
    if not IsBound(tab[fblocks[i]]) then 
      nr:=nr+1;
      tab[fblocks[i]]:=nr;
    fi;
  od;

  nr:=NrLeftBlocks(f);
  for i in [n+1..2*n] do 
    if gblocks[i]<=nr then 
      p[tab[gblocks[i]]]:=tab[fblocks[i]];
    fi;
  od;

  return PermList(p);
end);

#

InstallMethod(PermLeftQuoBipartition, "for a bipartition and bipartition",
[IsBipartition, IsBipartition],
function(f, g)
  local n, nr, fblocks, gblocks, p, i;

  if LeftBlocks(f)<>LeftBlocks(g) or RightBlocks(f)<>RightBlocks(g) then 
    Error("usage: the arguments must have equal left and right blocks,");
    return;
  fi;
  return PermLeftQuoBipartitionNC(f, g);
end);

# change representations...

InstallMethod(AsPartialPerm, "for a bipartition", [IsBipartition], 
function(f)
  local n, blocks, nrleft, im, out, i;

  if not IsPartialPermBipartition(f) then 
    Info(InfoWarning, 2, "<f> does not define a partial perm,");
    return fail;
  fi;
    
  n:=DegreeOfBipartition(f);
  blocks:=f!.blocks;
  nrleft:=NrLeftBlocks(f);
  im:=[1..n]*0;

  for i in [n+1..2*n] do 
    if blocks[i]<=nrleft then 
      im[blocks[i]]:=i-n;
    fi;
  od;

  out:=EmptyPlist(n);
  for i in [1..n] do 
    out[i]:=im[blocks[i]];
  od;
  return PartialPermNC(out);
end);

#

InstallMethod(AsPermutation, "for a bipartition", [IsBipartition], 
function(f)
  local n, blocks, nr, im, out, i;
  
  if not IsPermBipartition(f) then 
    Info(InfoWarning, 2, "<f> does not define a permutation,");
    return fail;
  fi;

  n:=DegreeOfBipartition(f);
  blocks:=f!.blocks;
  im:=EmptyPlist(n);

  for i in [n+1..2*n] do 
    im[blocks[i]]:=i-n;
  od;

  out:=EmptyPlist(n);
  for i in [1..n] do 
    out[i]:=im[blocks[i]];
  od;
  return PermList(out);
end);

#

InstallMethod(AsTransformation, "for a bipartition", [IsBipartition],
function(f)
  local n, blocks, nr, im, out, i;
  
  if not IsTransBipartition(f) then 
    Info(InfoWarning, 2, "<f> does not define a transformation,");
    return fail;
  fi;

  n:=DegreeOfBipartition(f);
  blocks:=f!.blocks;
  nr:=NrLeftBlocks(f);
  im:=EmptyPlist(n);

  for i in [n+1..2*n] do 
    if blocks[i]<=nr then 
      im[blocks[i]]:=i-n;
    fi;
  od;

  out:=EmptyPlist(n);
  for i in [1..n] do 
    out[i]:=im[blocks[i]];
  od;
  return TransformationNC(out);
end);

#

InstallMethod(AsBipartition, "for a permutation and zero",
[IsPerm, IsZeroCyc],
function(f, n) 
  return Bipartition([]);
end);

InstallMethod(AsBipartition, "for a permutation and pos int",
[IsPerm, IsPosInt],
function(f, n)
  return BipartitionByIntRepNC(Concatenation([1..n], ListPerm(f^-1, n)));
end);

InstallMethod(AsBipartition, "for a permutation", 
[IsPerm],
function(f) 
  return AsBipartition(f, LargestMovedPoint(f));
end);

#

InstallMethod(AsBipartition, "for a partial perm",
[IsPartialPerm],
function(f) 
  return AsBipartition(f, Maximum(DegreeOfPartialPerm(f),
   CodegreeOfPartialPerm(f)));
end);

InstallMethod(AsBipartition, "for a partial perm and zero",
[IsPartialPerm, IsZeroCyc],
function(f, n)
  return Bipartition([]);
end);

InstallMethod(AsBipartition, "for a partial perm and pos int",
[IsPartialPerm, IsPosInt],
function(f, n)
  local r, out, j, i;

  r:=n;
  out:=EmptyPlist(2*n);

  for i in [1..n] do 
    out[i]:=i;
    j:=PreImagePartialPerm(f, i);
    if j<>fail then 
      out[n+i]:=j;
    else 
      r:=r+1;
      out[n+i]:=r;
    fi;
  od;
  out:=BipartitionByIntRepNC(out); 
  SetIsPartialPermBipartition(out, true);
  return out;
end);

#

InstallMethod(AsBlockBijection, "for a partial perm",
[IsPartialPerm],
function(f) 
  return AsBlockBijection(f, Maximum(DegreeOfPartialPerm(f),
   CodegreeOfPartialPerm(f))+1);
end);

InstallMethod(AsBlockBijection, "for a partial perm and zero",
[IsPartialPerm, IsZeroCyc],
function(f, n)
  return Bipartition([]);
end);

# same as AsBipartition except that all undefined points are in a single block
# together with an extra (pair of) points.

InstallMethod(AsBlockBijection, "for a partial perm and pos int",
[IsPartialPerm, IsPosInt],
function(f, n)
  local bigblock, nr, out, i;

  if n<=Maximum(DegreeOfPartialPerm(f), CodegreeOfPartialPerm(f)) then 
    return fail;
  fi;

  nr:=0;
  out:=[1..2*n]*0;
  bigblock:=n;
  
  for i in [1..n-1] do 
    if i^f=0 then 
      if bigblock=n then 
        nr:=nr+1;
        bigblock:=nr;
      fi;
      out[i]:=bigblock;
    else 
      nr:=nr+1;
      out[i]:=nr;
      out[n+i^f]:=nr;
    fi;
  od;

  out[n]:=bigblock;
  out[2*n]:=bigblock;
  
  for i in [n+1..2*n-1] do 
    if out[i]=0 then 
      out[i]:=bigblock;
    fi;
  od;
  
  out:=BipartitionByIntRepNC(out); 
  SetIsBlockBijection(out, true);
  return out;
end);

#

InstallMethod(AsBipartition, "for a transformation",
[IsTransformation],
function(f)
  return AsBipartition(f, DegreeOfTransformation(f));
end);

InstallMethod(AsBipartition, "for a transformation and zero",
[IsTransformation, IsZeroCyc],
function(f, n)
  return Bipartition([]);
end);

InstallMethod(AsBipartition, "for a transformation and a positive integer",
[IsTransformation, IsPosInt],
function(f, n)
  local r, ker, out, g, i;
  
  if n<DegreeOfTransformation(f) then 
    #verify <f> is a transformation on [1..n]
    for i in [1..n] do 
      if i^f>n then 
        return fail;
      fi;
    od;
  fi;
  
  r:=RankOfTransformation(f, n);;
  ker:=FlatKernelOfTransformation(f, n); 
  
  out:=EmptyPlist(2*n);
  g:=List([1..n], x-> 0);

  #inverse of f
  for i in [1..n] do 
    g[i^f]:=i;
  od;

  for i in [1..n] do 
    out[i]:=ker[i];
    if g[i]<>0 then 
      out[n+i]:=ker[g[i]];
    else 
      r:=r+1;
      out[n+i]:=r;
    fi;
  od;
  out:=BipartitionByIntRepNC(out);
  SetIsTransBipartition(out, true);
  return out;
end);

#

InstallMethod(AsBipartition, "for a bipartition", [IsBipartition], IdFunc);

InstallMethod(AsBipartition, "for a bipartition", [IsBipartition, IsZeroCyc], 
function(f, n) return Bipartition([]); end);

InstallMethod(AsBipartition, "for a bipartition and pos int", 
[IsBipartition, IsPosInt],
function(f, n)
  local deg, blocks, out, nrblocks, nrleft, lookup, j, i;
 
  deg:=DegreeOfBipartition(f);
  if n=deg then 
    return f;
  fi;
  blocks:=f!.blocks;
  out:=[]; 
  nrblocks:=0; 
  
  if n<deg then
    for i in [1..n] do 
      out[i]:=blocks[i];
      if out[i]>nrblocks then 
        nrblocks:=nrblocks+1;
      fi;
    od;
    nrleft:=nrblocks;
    lookup:=EmptyPlist(NrBlocks(f));
    for i in [n+1..2*n] do
      j:=blocks[i+deg-n];
      if j>nrleft then 
        if not IsBound(lookup[j]) then 
          nrblocks:=nrblocks+1;
          lookup[j]:=nrblocks;
        fi;
        j:=lookup[j];
      fi;
      out[i]:=j;
    od;
  else # n>deg
    for i in [1..deg] do 
      out[i]:=blocks[i];
    od;
    nrblocks:=NrLeftBlocks(f);
    for i in [deg+1..n] do 
      nrblocks:=nrblocks+1;
      out[i]:=nrblocks;
    od;
    nrleft:=nrblocks; #=n-deg+NrLeftBlocks(f)
    for i in [n+1..n+deg] do 
      if blocks[i-n+deg]<=nrleft-n+deg then #it's a left block
        out[i]:=blocks[i-n+deg];
      else
        out[i]:=blocks[i-n+deg]+n-deg;
      fi;
    od;
    nrblocks:=NrBlocks(f)+n-deg;
    for i in [n+deg+1..2*n] do 
      nrblocks:=nrblocks+1;
      out[i]:=nrblocks;
    od;
  fi;
  out:=Objectify(BipartitionType, rec(blocks:=out));
  SetDegreeOfBipartition(out, n);
  SetNrBlocks(out, nrblocks);
  SetNrLeftBlocks(out, nrleft);
  return out;
end);

#properties/attributes

# linear - attribute

# returns a blist <out> for the Left blocks so that <out[i]> is <true> if
# and only the <i>th block of <f> is a transverse block.

InstallMethod(TransverseBlocksLookup, "for a bipartition", [IsBipartition], 
function(f)
  local n, k, blocks, out, i;
  
  if IsBound(f!.lookup) then 
    return f!.lookup;
  fi;

  n:=DegreeOfBipartition(f);
  k:=NrLeftBlocks(f);
  blocks:=f!.blocks;
  out:=BlistList([1..k], []);

  for i in [1..n] do 
    if blocks[i+n]<=k then 
      out[blocks[i+n]]:=true;
    fi;
  od;

  f!.lookup:=out;
  return out;
end);

#

InstallMethod(RankOfBipartition, "for a bipartition",
[IsBipartition],
function(f)
  return Number(TransverseBlocksLookup(f), x-> x=true);
end);

# return the classes of <f> as a list of lists

InstallMethod(ExtRepOfBipartition, "for a bipartition",
[IsBipartition],
function(f)
  local n, blocks, ext, i;

  n:=DegreeOfBipartition(f);
  blocks:=f!.blocks;
  ext:=[];
  
  for i in [1..2*n] do 
    if not IsBound(ext[blocks[i]]) then 
      ext[blocks[i]]:=[];
    fi;
    if i<=n then 
      Add(ext[blocks[i]], i);
    else
      Add(ext[blocks[i]], -(i-n));
    fi;
  od;

  return ext;
end);

#

InstallMethod(IsBlockBijection, "for a bipartition", 
[IsBipartition], 
function(f) 
  return NrBlocks(f)=NrLeftBlocks(f) and NrRightBlocks(f)=NrLeftBlocks(f);
end);

#

InstallMethod(IsUniformBlockBijection, "for a bipartition", 
[IsBipartition], 
function(f)
  local blocks, n, sizesleft, sizesright, i;
  
  if not IsBlockBijection(f) then 
    return false;
  fi;
  
  blocks:=f!.blocks;
  n:=DegreeOfBipartition(f);
  sizesleft:=[1..NrBlocks(f)]*0;
  sizesright:=[1..NrBlocks(f)]*0;

  for i in [1..n] do 
    sizesleft[blocks[i]]:=sizesleft[blocks[i]]+1;
  od;
  for i in [n+1..2*n] do 
    sizesright[blocks[i]]:=sizesright[blocks[i]]+1;
  od;
  for i in [1..NrBlocks(f)] do 
    if sizesright[i]<>sizesleft[i] then 
      return false;
    fi;
  od;
  
  return true;
end);

#

InstallMethod(IsPartialPermBipartition, "for a bipartition", 
[IsBipartition], 
function(f)
  return NrLeftBlocks(f)=DegreeOfBipartition(f) 
    and NrRightBlocks(f)=DegreeOfBipartition(f);
end);

# a bipartition is a transformation if and only if the second row is a
# permutation of [1..n], where n is the degree. 

InstallMethod(IsTransBipartition, "for a bipartition",
[IsBipartition], 
function(f)
  return NrLeftBlocks(f)=NrTransverseBlocks(f) 
   and NrRightBlocks(f)=DegreeOfBipartition(f);
end);

#

InstallMethod(IsDualTransBipartition, "for a bipartition", [IsBipartition], 
function(f)
  return NrRightBlocks(f)=NrTransverseBlocks(f) 
   and NrLeftBlocks(f)=DegreeOfBipartition(f);
end);

#

InstallMethod(IsPermBipartition, "for a bipartition",
[IsBipartition], 
function(f)
  return IsPartialPermBipartition(f) and NrTransverseBlocks(f)=DegreeOfBipartition(f);
end);

# creating

# xx^* - linear - 2*degree - attribute

InstallMethod(LeftOne, "for a bipartition", [IsBipartition],
function(f)
  local n, next, blocks, lookup, table, out, i;

  n:=DegreeOfBipartition(f);
  next:=NrLeftBlocks(f);
  blocks:=f!.blocks;
  lookup:=TransverseBlocksLookup(f);
  table:=[];
  out:=[];

  for i in [1..n] do 
    out[i]:=blocks[i];
    if lookup[blocks[i]] then 
      out[i+n]:=blocks[i];
    elif IsBound(table[blocks[i]]) then 
      out[i+n]:=table[blocks[i]];
    else 
      next:=next+1;
      table[blocks[i]]:=next;
      out[i+n]:=next;
    fi;
  od;

  out:=Objectify(BipartitionType, rec(blocks:=out));
  
  SetDegreeOfBipartition(out, n);
  SetNrLeftBlocks(out, NrLeftBlocks(f));
  SetNrBlocks(out, next);
  SetRankOfBipartition(out, RankOfBipartition(f));
  return out;
end);

# linear - 2*degree

InstallMethod(StarOp, "for a bipartition", [IsBipartition],
function(f)
  local n, blocks, table, out, next, nrleft, i;

  n:=DegreeOfBipartition(f);
  blocks:=f!.blocks;
  table:=[];
  out:=[];
  next:=0;

  for i in [1..n] do 
    if IsBound(table[blocks[i+n]]) then 
      out[i]:=table[blocks[i+n]];
    else
      next:=next+1;
      table[blocks[i+n]]:=next;
      out[i]:=next;
    fi;
  od;

  nrleft:=next;

  for i in [1..n] do 
    if IsBound(table[blocks[i]]) then 
      out[i+n]:=table[blocks[i]];
    else
      next:=next+1;
      table[blocks[i]]:=next;
      out[i+n]:=next;
    fi;
  od;

  out:=Objectify(BipartitionType, rec(blocks:=out)); 
  
  SetDegreeOfBipartition(out, Length(blocks)/2);
  SetNrLeftBlocks(out, nrleft);
  SetNrBlocks(out, next);
  SetRankOfBipartition(out, RankOfBipartition(f));
  return out;
end);  

# linear - 2*degree 

InstallMethod(RightProjection, "for a bipartition",
[IsBipartition],
function(f)
  local n, blocks, table, out, next, nrleft, lookup, i;

  n:=DegreeOfBipartition(f);
  blocks:=f!.blocks;
  table:=[];
  out:=[];
  next:=0;

  for i in [1..n] do 
    if IsBound(table[blocks[i+n]]) then 
      out[i]:=table[blocks[i+n]];
    else
      next:=next+1;
      table[blocks[i+n]]:=next;
      out[i]:=next;
    fi;
  od;

  nrleft:=next;
  table:=[];
  lookup:=TransverseBlocksLookup(f);

  for i in [1..n] do 
    if blocks[i+n]<=NrLeftBlocks(f) and lookup[blocks[i+n]] then 
      out[i+n]:=out[i];
    elif IsBound(table[blocks[i+n]]) then 
      out[i+n]:=table[blocks[i+n]];
    else
      next:=next+1;
      table[blocks[i+n]]:=next;
      out[i+n]:=next;
    fi;
  od;

  out:=Objectify(BipartitionType, rec(blocks:=out));
  
  SetDegreeOfBipartition(out, n);
  SetNrLeftBlocks(out, nrleft);
  SetNrBlocks(out, next);
  return out;
end);

#

InstallMethod(RandomBipartition, "for a pos int", [IsPosInt],
function(n)
  local out, nrblocks, vals, j, nrleft, i;

  out:=EmptyPlist(2*n);
  nrblocks:=0;
  vals:=[1];

  for i in [1..n] do 
    j:=Random(vals);
    if j=nrblocks+1 then 
      nrblocks:=nrblocks+1;
      Add(vals, nrblocks+1);
    fi;
    out[i]:=j;
  od;

  nrleft:=nrblocks;

  for i in [1..n] do 
    j:=Random(vals);
    if j=nrblocks+1 then 
      nrblocks:=nrblocks+1;
      Add(vals, nrblocks+1);
    fi;
    out[i+n]:=j;
  od;

  out:=Objectify(BipartitionType, rec(blocks:=out)); 
  
  SetDegreeOfBipartition(out, n);
  SetNrLeftBlocks(out, nrleft);
  SetNrBlocks(out, nrblocks);

  return out;
end);

# c function

InstallGlobalFunction(Bipartition, 
function(classes)
  local n, copy, i, j;
 
  if not ForAll(classes, IsList) or not ForAll(classes, IsDuplicateFree) then 
    Error("<classes> must consist of duplicate-free lists,");
    return;
  fi;

  if not ForAll(classes, x-> ForAll(x, i-> IsPosInt(i) or IsNegInt(i))) then 
    Error("<classes> must consist of positive and negative integers,");
    return;
  fi;
  
  copy:=Union(classes);
  if not (copy=classes or copy=Concatenation([Minimum(copy)..-1],
    [1..Maximum(copy)])) then 
    Error("the union of <classes> must be [-n..-1, 1..n],");
    return;
  fi;

  n:=Sum(List(classes, Length))/2;
  copy:=List(classes, ShallowCopy);
  for i in [1..Length(copy)] do
    for j in [1..Length(copy[i])] do 
      if copy[i][j]<0 then 
        copy[i][j]:=AbsInt(copy[i][j])+n;
      fi;
    od;
  od;
  
  Perform(copy, Sort);
  Sort(copy);

  for i in [1..Length(copy)] do
    for j in [1..Length(copy[i])] do 
      if copy[i][j]>n then 
        copy[i][j]:=-copy[i][j]+n;
      fi;
    od;
  od;
  return BipartitionNC(copy);
end);

#

InstallGlobalFunction(BipartitionNC, 
function(classes)
  local blocks, n, rank, nrleft, nrblocks, k, out, i, j;

  blocks:=[];
  n:=Sum(List(classes, Length))/2;
  rank:=0; 
  nrleft:=0;
  nrblocks:=Length(classes);

  for i in [1..Length(classes)] do
    k:=0; # detect if the class is transverse or not
    for j in classes[i] do 
      if j<0 then 
        blocks[-j+n]:=i;
      else 
        nrleft:=i;
        blocks[j]:=i;
      fi;
    od;
  od;

  out:=Objectify(BipartitionType, rec(blocks:=blocks)); 
  
  SetDegreeOfBipartition(out, n);
  SetNrLeftBlocks(out, nrleft);
  SetExtRepOfBipartition(out, AsList(classes));
  SetNrBlocks(out, nrblocks);

  return out;
end);

#

InstallMethod(OneMutable, "for a bipartition",
[IsBipartition], x-> IdentityBipartition(DegreeOfBipartition(x)));

#

InstallMethod(OneMutable, "for a bipartition collection",
[IsBipartitionCollection], x->
IdentityBipartition(DegreeOfBipartitionCollection(x)));

#

InstallMethod(IdentityBipartition, "for a positive integer", [IsPosInt],
function(n)
  local blocks, out, i;
  
  blocks:=EmptyPlist(2*n);
  for i in [1..n] do 
    blocks[i]:=i;
    blocks[i+n]:=i;
  od;
  
  out:=Objectify(BipartitionType, rec(blocks:=blocks));

  SetDegreeOfBipartition(out, n);
  SetRankOfBipartition(out, n);
  SetNrLeftBlocks(out, n);
  SetNrBlocks(out, n);

  return out;
end);

#

InstallMethod(BipartitionByIntRepNC, "for a list", [IsList],
function(blocks)
  local n, next, seen, nrleft, rank, lookup, out, i;

  n:=Length(blocks)/2;
  next:=0;
  seen:=BlistList([1..2*n], []);

  for i in [1..n] do 
    if not seen[blocks[i]] then 
      next:=next+1;
      seen[blocks[i]]:=true;
    fi;
  od;
  
  nrleft:=next; 

  for i in [n+1..2*n] do 
    if not seen[blocks[i]] then #new block
      next:=next+1;
      seen[blocks[i]]:=true;
    fi;
  od;

  out:=Objectify(BipartitionType, rec(blocks:=blocks)); 

  SetDegreeOfBipartition(out, n);
  SetNrLeftBlocks(out, nrleft);
  SetNrBlocks(out, next);
  return out;
end);

#

InstallMethod(BipartitionByIntRep, "for a list", [IsList],
function(blocks)
  local n, next, seen, nrleft, rank, lookup, out, i;

  n:=Length(blocks);
  if not IsEvenInt(n) then 
    Error("the length of <blocks> must be an even integer,");
    return;
  fi;
  
  n:=n/2;
  if not ForAll(blocks, IsPosInt) then 
    Error("the elements of <blocks> must be positive integers,");
    return;
  fi;

  next:=0;
  seen:=BlistList([1..2*n], []);

  for i in [1..n] do 
    if not seen[blocks[i]] then 
      next:=next+1;
      if blocks[i]<>next then 
        Error("expected ", next, " but found ", blocks[i], ",");
        return;
      fi;
      seen[blocks[i]]:=true;
    fi;
  od;
  
  nrleft:=next; 

  for i in [n+1..2*n] do 
    if not seen[blocks[i]] then 
      next:=next+1;
      if blocks[i]<>next then 
        Error("expected ", next, " but found ", blocks[i], ",");
        return;
      fi;
      seen[blocks[i]]:=true;
   fi;
  od;

  out:=Objectify(BipartitionType, rec(blocks:=blocks)); 

  SetDegreeOfBipartition(out, n);
  SetNrLeftBlocks(out, nrleft);
  SetNrBlocks(out, next);
  return out;
end);

#technical

# LambdaConjugator: f and g have equal left blocks (rho value)
# JDM: this will be better in c...

InstallGlobalFunction(BipartRightBlocksConj,
function(f, g)
  local n, fblocks, gblocks, nr, lookup, next, seen, src, dst, i;

  n:=DegreeOfBipartition(f);
  fblocks:=f!.blocks;     
  gblocks:=g!.blocks;
  nr:=NrLeftBlocks(f);

  lookup:=[];
  next:=0; 
  seen:=BlistList([1..2*n], []);
  for i in [n+1..2*n] do 
    if not seen[gblocks[i]] then 
      next:=next+1; 
      seen[gblocks[i]]:=true;
      if gblocks[i]<=nr then #connected block
        lookup[gblocks[i]]:=next;
      fi;
    fi;
  od;
  
  src:=[]; dst:=[];
  next:=0; 
  seen:=BlistList([1..2*n], []);
  for i in [n+1..2*n] do 
    if not seen[fblocks[i]] then 
      next:=next+1; 
      seen[fblocks[i]]:=true;
      if fblocks[i]<=nr then #connected block
        Add(src, next);
        Add(dst, lookup[fblocks[i]]);
      fi;
    fi;
  od; 

  return MappingPermListList(src, dst);
end);

# StabiliserAction

InstallGlobalFunction(OnRightBlocksBipartitionByPerm,
function(f, p)
  local n, out, blocks, tab1, tab2, next, q, i;
  
  if IsOne(p) then 
    return f;
  fi;
  
  n:=DegreeOfBipartition(f);
  out:=EmptyPlist(2*n);
  blocks:=f!.blocks;

  tab1:=EmptyPlist(2*n);
  tab2:=EmptyPlist(2*n);
  next:=0;
  q:=p^-1;
  
  for i in [n+1..2*n] do 
    if not IsBound(tab1[blocks[i]]) then 
      next:=next+1;
      tab1[blocks[i]]:=next^q;
      tab2[next]:=blocks[i];
    fi;
  od;
  
  for i in [1..n] do 
    out[i]:=blocks[i];
    out[i+n]:=tab2[tab1[blocks[i+n]]];
  od;

  out:=Objectify(BipartitionType, rec(blocks:=out)); 
  
  SetDegreeOfBipartition(out, n);
  SetNrLeftBlocks(out, NrLeftBlocks(f));
  SetNrBlocks(out, NrBlocks(f));
  SetRankOfBipartition(out, RankOfBipartition(f));
  SetTransverseBlocksLookup(out, TransverseBlocksLookup(f));

  if HasLeftBlocks(f) then 
    SetLeftBlocks(out, LeftBlocks(f));
  fi;
  if HasRightBlocks(f) then 
    SetRightBlocks(out, RightBlocks(f));
  fi;

  return out;
end);

#view/print/display

InstallMethod(ViewObj, "for a bipartition",
[IsBipartition],
function(f)
  local ext, i;

  if DegreeOfBipartition(f)=0 then 
    Print("<empty bipartition>");
    return;
  fi;
  if IsBlockBijection(f) then 
    Print("<block bijection: ");
  else 
    Print("<bipartition: ");
  fi;
  ext:=ExtRepOfBipartition(f);
  Print(ext[1]);
  for i in [2..Length(ext)] do 
    Print(", ", ext[i]);
  od;
  Print(">");
  return;
end);

#

InstallMethod(PrintObj, "for a bipartition",
[IsBipartition], 
function(f)
  Print("Bipartition( ", ExtRepOfBipartition(f), " )");
  return;
end);

#

InstallMethod(PrintObj, "for a bipartition collection",
[IsBipartitionCollection],
function(coll) 
  local i;

  Print("[ ");
  for i in [1..Length(coll)] do 
    if not i=1 then Print(" "); fi;
    Print(coll[i]);
    if not i=Length(coll) then 
      Print(",\n");
    else
      Print(" ]\n");
    fi;
  od;
  return;
end);

# required to beat the method for bipartition collections...

InstallMethod(PrintObj, "for an equivalence class of bipartitions",
[IsBipartitionCollection and IsEquivalenceClass],
function(c) 
  Print( "{", Representative( c ), "}" );
  return;
end);

#collections

InstallMethod(DegreeOfBipartitionCollection, "for a bipartition collection",
[IsBipartitionCollection], 
function(coll)
  local deg;

  if IsBipartitionSemigroup(coll) then 
    return DegreeOfBipartitionSemigroup(coll);
  fi;
  
  deg:=DegreeOfBipartition(coll[1]);
  if not ForAll(coll, x-> DegreeOfBipartition(x)=deg) then 
    Error("usage: collection of bipartitions of equal degree,");
    return;
  fi;
  
  return deg;
end);

# Results:

# n=1 partitions=2 idempots=2
# n=2 partitions=15 idempots=12
# n=3 partitions=203 idempots=114
# n=4 partitions=4140 idempots=1512
# n=5 partitions=115975 idempots=25826
# n=6 partitions=4213597 idempots=541254, 33 seconds
# n=7 partitions=190899322 idempots=13479500, 1591 seconds

