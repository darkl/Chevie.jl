using Test, Chevie

@testset "Twisted unipotent values" begin
  @testset "$name in characteristic $p" for (name,n,p,q) in
    ((:u,4,0,3),(:su,3,2,2),(:sl,3,0,2),
     (Symbol("so-"),8,0,3),(Symbol("spin-"),10,0,3),
     (Symbol("3D4"),0,0,3),(Symbol("3D4"),0,2,2),
     (Symbol("2E6"),0,0,5),(Symbol("2E6"),0,2,2),(Symbol("2E6"),0,3,3),
     (Symbol("2E6sc"),0,0,5),
     (Symbol("2B2"),0,2,root(8)),(Symbol("2G2"),0,3,root(27)),
     (Symbol("2F4"),0,2,root(8)))
    q=q*big(1)
    w=n==0 ? rootdatum(name) : rootdatum(name,n)
    N=nref(w isa Spets ? Group(w) : w)
    u=UnipotentClasses(w,p)
    t=UnipotentValues(u;q,classes=true)
    d=degrees(UnipotentCharacters(w),q)
    id=only(j for (j,(c,a)) in enumerate(t.classes) if t.uc.classes[c].dimBu==N)
    @test t.scalar[:,id]==d
    @test all(isone,t.scalar[findfirst(isone,d),:])
    @test t.scalar[findfirst(==(q^N),d),:]==
          [j==id ? q^N : 0 for j in eachindex(t.classes)]
    @test sum(t.cardClass)==q^(2N)
    @test all(x->x>0 && denominator(x)==1,t.cardClass)
  end

  @testset "Field action on the centre" begin
    # Shoji, math/0507057, Theorem 3.4; Lübeck--Shoji, 2408.16960,
    # Theorem 2.19 and §§3.4, 9.2: q on SL, -q on SU, odd 2D and 2E6.
    for (name,n,p,q,count) in ((:sl,3,0,2,1),(:sl,3,0,4,3),
                              (:su,3,2,2,3),(:su,3,2,4,1),
                              (Symbol("spin-"),10,0,3,4),
                              (Symbol("spin-"),10,0,9,2),
                              (Symbol("2E6sc"),0,0,5,3),
                              (Symbol("2E6sc"),0,0,7,1))
      w=n==0 ? rootdatum(name) : rootdatum(name,n)
      u=UnipotentClasses(w,p)
      before=deepcopy(u.springerseries)
      t=UnipotentValues(u;q,classes=true)
      @test count==sum(c->t.uc.classes[c[1]].dimBu==0,t.classes)
      @test u.springerseries==before
    end
  end
end

include("data/unipotenttwisted.jl")

@testset "Published Suzuki/Ree tables" begin
  # Source row orders retain conjugate cuspidal labels. The Suzuki [1,3]
  # label induces to the [1,3] Harish-Chandra series in 2F4.
  for (name,p,fixture,rows,cols) in
    (("2B2",2,fixture_2B2,[1,4,3,2],1:4),
     ("2G2",3,fixture_2G2,[1,8,4,6,7,2,5,3],1:7),
     ("2F4",2,fixture_2F4,[1,21,5,4,18,15,10,8,3,20,9,2,19,11,12,14,13,16,6,7,17],
      [1,2,3,18,19,4,5,6,7,8,9,10,11,12,13,14,15,16,17]))
    @testset "$name, q0=$q0" for q0 in (big(1),big(p),Mvp(:v))
      w=rootdatum(name)
      u=UnipotentClasses(w,p)
      q=root(p)*q0 # CHEVIE parameter sqrt(Q), Q=p*q0².
      t=UnipotentValues(u;q,classes=true)
      f=fixture(q0)
      @test t.scalar[:,cols]==f.values[rows,:]
      @test t.cardClass[cols]==f.sizes
      g=GreenTable(u;q,classes=true).scalar[1:nconjugacy_classes(w),cols]
      # The source uses a different order of rational tori.
      @test all(row->any(==(row),eachrow(g)),eachrow(f.green))
    end
  end
end

@testset "Published 2E6 Green functions and cuspidal values" begin
  for p in (0,2,3)
    @testset "characteristic $p" begin
      q=Mvp(:q)
      w=rootdatum("2E6")
      u=UnipotentClasses(w,p)
      t=UnipotentValues(u;q,classes=true)
      f=p==2 ? fixture_2E6_2(q) : fixture_2E6_good(q)
      torusnames=replace.(f.tori,"\\\\emptyset"=>"A_0")
      order=[only(findall(==(s),classinfo(w).classnames)) for s in torusnames]
      g=GreenTable(u;q,classes=true).scalar[order,:]
      refgreen=f.green; sizes=f.sizes
      if p==3
        # Lübeck--Shoji, 2408.16960, Theorem 9.16: same principal
        # Green functions, with the regular class split into three.
        refgreen=hcat(refgreen[:,1:end-1],repeat(refgreen[:,end:end],1,3))
        sizes=vcat(sizes[1:end-1],fill(sizes[end]//3,3))
      end
      expected=[(refgreen[:,j],sizes[j]) for j in axes(refgreen,2)]
      actual=[(g[:,j],t.cardClass[j]) for j in axes(g,2)]
      @test length(expected)==length(actual)
      @test all(x->count(==(x),actual)==count(==(x),expected),expected)
      almost=fourier(UnipotentCharacters(w))*t.scalar
      if p==2
        # Hetz, 2309.09915v2, Lemma 8.5 and Table 7. CHEVIE's Cd2
        # Fourier row 13 is the negative of Hetz's R_(E6,-1).
        columns=[only(j for (j,(c,b)) in enumerate(t.classes)
                      if u.classes[c].name==name && b==a)
                 for name in ("D_4","D_5","E_6") for a in 1:2]
        @test Diagonal([-1,1,1])*almost[[13,28,14],columns]==
          [q^5 -q^5 -q^3 q^3 -q^2 q^2;
           q^7-q^6 -q^7+q^6 q^4 -q^4 0 0;
           -q^8 q^8 0 0 0 0]
        @test all(iszero,almost[[29,30],:])
      elseif p==3
        # Hetz, 1901.06225, Proposition 4.5.
        for k in 1:2
          @test almost[28+k,:]==[u.classes[c].dimBu==0 ? q^3*E(3,k*(a-1)) : 0
                                 for (c,a) in t.classes]
        end
        @test all(iszero,almost[[13,14,28],:])
      else
        @test all(iszero,almost[[13,14,28,29,30],:])
      end
    end
  end
end

@testset "Labelled unitary tables" begin
  # Simpson--Frame, SU3.2; Lübeck, uniGU4 (same pinned source as fixtures).
  for n in (3,4), form in (:u,:su), p in (2,3,5)
    q=big(p); w=rootdatum(form,n)
    t=UnipotentValues(UnipotentClasses(w,p);q,classes=true)
    parts=n==3 ? [[1,1,1],[2,1],[3]] : [[1,1,1,1],[2,1,1],[2,2],[3,1],[4]]
    expected=n==3 ? [q^3 0 0; q*(q-1) -q 0; 1 1 1] :
      [q^6 0 0 0 0; q^3*(q^2-q+1) q^3 0 0 0;
       q^2*(q^2+1) q^2 q^2 0 0; q*(q^2-q+1) -q*(q-1) q q 0; 1 1 1 1 1]
    symbols=[[CharSymbol([reverse(part).+(0:length(part)-1)])] for part in parts]
    rows=[only(findall(==(s),UnipotentCharacters(w).charSymbols)) for s in symbols]
    for (j,(c,a)) in enumerate(t.classes)
      col=only(findall(==(t.uc.classes[c].parameter),parts))
      @test t.scalar[rows,j]==expected[:,col]
    end
  end
end

@testset "Published 3D4 and 2D4 tables" begin
  for p in (0,2), q in (Mvp(:q)*big(1),big(p==2 ? 2 : 3))
    w=rootdatum("3D4"); t=UnipotentValues(UnipotentClasses(w,p);q,classes=true)
    f=fixture_triality(q); vals=f.values; sizes=f.sizes
    names=p==2 ? ["11111111","(22)1111","2222","3311","3311","44","62","62"] :
                  ["11111111","221111","3221","3311","3311","53","71"]
    if p==2
      # Spaltenstein (1982), Theorem 2, Table 2: the extra regular pair.
      cusp=[0,0,-1,1,1,-1,0,0]*q^2//2
      vals=hcat(vals[:,1:6],vals[:,7]+cusp,vals[:,7]-cusp)
      sizes=vcat(sizes[1:6],fill(sizes[7]//2,2))
    end
    columns=[(name,i>1 && names[i-1]==name ? 2 : 1) for (i,name) in enumerate(names)]
    cols=[only(j for (j,(c,a)) in enumerate(t.classes) if (t.uc.classes[c].name,a)==label) for label in columns]
    @test t.scalar[[1,5,3,7,8,4,6,2],cols]==vals
    @test t.cardClass[cols]==sizes
  end
  symbols=[[[0,1,2,3,4],[1,2,3]],[[0,1,2,3],[1,3]],[[0,1,2,4],[1,2]],
           [[0,1,3],[2]],[[1,2,3],[0]],[[0,2,3],[1]],[[0,1,2],[3]],
           [[0,1,4],[1]],[[1,3],Int[]],[[0,4],Int[]]]
  parts=[[1,1,1,1,1,1,1,1],[2,2,1,1,1,1],[3,1,1,1,1,1],[3,2,2,1],
         [3,3,1,1],[3,3,1,1],[5,1,1,1],[5,3],[7,1]]
  for q in (big(3),big(5),Mvp(:q)*big(1))
    w=rootdatum("pso-",8); t=UnipotentValues(UnipotentClasses(w);q,classes=true)
    rows=[only(findall(==([CharSymbol(s)]),UnipotentCharacters(w).charSymbols)) for s in symbols]
    f=fixture_2D4(q)
    expected=[(parts[j],f.values[:,j],f.sizes[j]) for j in eachindex(parts)]
    actual=[(sort(t.uc.classes[c].parameter;rev=true),t.scalar[rows,j],t.cardClass[j]) for (j,(c,a)) in enumerate(t.classes)]
    @test length(actual)==length(expected)
    @test all(x->count(==(x),actual)==count(==(x),expected),expected)
  end
end

@testset "Field validity and scalar conventions" begin
  for (name,p) in (("2B2",2),("2G2",3),("2F4",2))
    w=rootdatum(name)
    @test UnipotentClasses(w).p==p
    @test_throws ErrorException UnipotentClasses(w,5)
    for q in (1,p,root(5))
      @test_throws ErrorException UnipotentValues(UnipotentClasses(w,p);q)
    end
  end
  @test_throws ErrorException UnipotentValues(UnipotentClasses(rootdatum("3D4"));q=2)
  @test_throws ErrorException UnipotentValues(UnipotentClasses(rootdatum("2E6"));q=3)
  @test_throws ErrorException UnipotentValues(UnipotentClasses(rootdatum("so-",8),2);q=2)
  w=rootdatum("2F4"); u=deepcopy(UnipotentClasses(w,2))
  c=only(c for c in u.classes if c.name=="F_4(a_2)")
  @test nconjugacy_classes(c.AuF)==3
  @test length(c.Au)==8
  t=UnipotentValues(u;q=root(8),classes=true)
  s=only(s for s in u.springerseries if get(s,:hc,0)==5)
  s[:scalars]=[1]
  changed=UnipotentValues(u;q=root(8),classes=true)
  @test changed.cardClass==t.cardClass
  almost=fourier(UnipotentCharacters(w))*changed.scalar
  @test almost[11,:]==[u.classes[c].dimBu==0 ? 8E(4,a-1) : 0 for (c,a) in t.classes]
end

@testset "Simply connected 2E6 field branches" begin
  # Lübeck--Shoji, 2408.16960, §§9.2,9.8; Digne--Michel (1991),
  # Proposition 13.20: unipotent characters pull back from the adjoint form.
  for (p,q) in ((2,2),(2,4),(3,3),(0,5),(0,7))
    a=UnipotentValues(UnipotentClasses(rootdatum("2E6"),p);q,classes=true)
    b=UnipotentValues(UnipotentClasses(rootdatum("2E6sc"),p);q,classes=true)
    labels(t)=[(t.uc.classes[c].name,t.scalar[:,j]) for (j,(c,d)) in enumerate(t.classes)]
    x,y=labels(a),labels(b)
    @test all(l->l in x,y)
    for l in unique(x)
      @test sum(a.cardClass[findall(==(l),x)])==sum(b.cardClass[findall(==(l),y)])
    end
    @test sum(b.cardClass)==big(q)^72
  end
end

@testset "Higher rank odd-characteristic 2D" begin
  for n in (5,6,8), form in ("so-","pso-","spin-")
    # Rank 8 is covered in the adjoint form; smaller ranks check isogenies.
    n==8 && form!="pso-" && continue
    w=rootdatum(form,2n);q=big(3)
    t=UnipotentValues(UnipotentClasses(w);q,classes=true)
    id=only(j for (j,(c,a)) in enumerate(t.classes) if t.uc.classes[c].dimBu==n*(n-1))
    @test t.scalar[:,id]==degrees(UnipotentCharacters(w),q)
    @test sum(t.cardClass)==q^(2n*(n-1))
    @test all(x->denominator(x)==1,t.scalar)
  end
end

@testset "Exact phases and symbolic field branches" begin
  @testset "Complex comparison factor" begin
    w=rootdatum("3D4");u=deepcopy(UnipotentClasses(w,2))
    u.springerseries[2][:scalars]=[E(4)]
    t=UnipotentValues(u;q=2,classes=true)
    a=fourier(UnipotentCharacters(w))*t.scalar
    @test a[8,:]==[u.classes[c].dimBu==0 ? 4E(4)*(-1)^(b-1) : 0 for (c,b) in t.classes]
  end
  @testset "Large Suzuki parameter" begin
    q=root(2)*2^35
    t=UnipotentValues(UnipotentClasses(rootdatum("2B2"));q,classes=true)
    @test sum(t.cardClass)==big(2)^284
  end
  @testset "Symbolic central branch for $name" for (name,n,p,q) in
      ((:su,3,2,2),(Symbol("spin-"),10,0,3),(Symbol("2E6sc"),0,2,2))
    w=n==0 ? rootdatum(name) : rootdatum(name,n)
    t=UnipotentValues(UnipotentClasses(w,p;q);classes=true)
    v=UnipotentValues(UnipotentClasses(w,p);q,classes=true)
    @test map(x->x(;q),t.scalar)==v.scalar
    @test t.classes==v.classes
  end
end


@testset "Field branches in XTable and GreenTable" begin
  # Lübeck--Shoji, arXiv:2408.16960, Theorem 2.19 and §§3.4,9.2:
  # discarded central characters cannot be recovered by evaluating q alone.
  for (name,n,p,branch,q,regular) in
      ((:su,3,2,1,2,3),(:su,3,2,2,4,1),(:sl,3,2,2,4,3),
       (Symbol("spin-"),10,0,1,3,4),(Symbol("spin-"),10,0,3,9,2),
       (Symbol("2E6sc"),0,0,1,5,3),(Symbol("2E6sc"),0,0,5,7,1))
    @testset "$name, branch=$branch, q=$q" begin
      w=n==0 ? rootdatum(name) : rootdatum(name,n)
      u=UnipotentClasses(w,p;q=branch)
      before=deepcopy(u.springerseries)
      for table in (XTable,GreenTable), classes in (false,true)
        @test_throws "incompatible field branch" table(u;q,classes)
      end
      # The higher-level API still reconstructs the requested field branch.
      t=UnipotentValues(u;q,classes=true)
      @test count(c->t.uc.classes[c[1]].dimBu==0,t.classes)==regular
      @test u.springerseries==before
    end
  end
  @testset "Compatible field parameters" begin
    for (form,branch,q,regular) in
        ((:su,1,4,1),(:su,2,2,3),(:su,2,8,3),
         (:sl,1,4,3),(:sl,2,2,1),(:sl,2,8,1))
      u=UnipotentClasses(rootdatum(form,3),2;q=branch)
      for table in (XTable,GreenTable)
        t=table(u;q,classes=true)
        @test count(c->t.uc.classes[c[1]].dimBu==0,t.classes)==regular
        if form==:su && q==2
          # |SU3(2)|=216, centralizers 216,24,12,12,12. The total
          # 64 alone cannot distinguish [1,9,18,18,18] from [1,9,54].
          @test sort(t.cardClass)==[1,9,18,18,18]
        end
      end
    end
  end
end

@testset "Unsupported twisted products retain no silent defaults" begin
  for (name,p) in (("2E6",0),("2E6",2),("2B2",2),("2G2",3),("2F4",2)), reverse in (false,true)
    w=rootdatum(name); a=coxgroup(:A,1)
    product=reverse ? Chevie.Cosets.extprod(a,w) : Chevie.Cosets.extprod(w,a)
    @test_throws "products with twisted normalization data" UnipotentClasses(product,p)
  end
end

@testset "Labelled 60_8 normalization in 2E6" begin
  # Lübeck--Shoji, arXiv:2408.16960v1, §9.10: gamma=(-1)^(a_E-d_u).
  # The printed (9.10.1)-(2) omit this pair; audit its labels explicitly.
  w=rootdatum("2E6"); info=charinfo(w)
  i=only(findall(==([[60,8]]),info.charparams))
  @test info.a[i]==7
  for p in (0,2,3)
    u=UnipotentClasses(w,p); s=u.springerseries[1]
    c,a=s[:locsys][i]
    @test u.classes[c].name=="A_3{+}A_1"
    @test u.classes[c].dimBu==8
    @test a==charinfo(u.classes[c].Au).positionId
    @test s[:greenSigns][i]==-1
  end
end

@testset "Exact integer field representations" begin
  w=rootdatum(:su,3); u=UnipotentClasses(w,2)
  for q in (2//1,2E(1)), table in (XTable,GreenTable)
    for classes in (false,true)
      @test_throws "incompatible field branch" table(u;q,classes)
    end
    t=table(UnipotentClasses(w,2;q=2);q,classes=true)
    @test sort(t.cardClass)==[1,9,18,18,18]
  end
end
