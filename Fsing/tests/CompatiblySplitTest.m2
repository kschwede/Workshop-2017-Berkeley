TEST /// 
R=ZZ/2[x_{21},x_{31},x_{32},x_{41},x_{42},x_{43}]
u=x_{41}*(x_{31}*x_{42}-x_{41}*x_{32})*(x_{41}-x_{21}*x_{42}-x_{31}*x_{43}+x_{21}*x_{32}*x_{43})
time CompatibleIdeals=findAllCompatibleIdeals (u)
answer=  {ideal(x_{21}*x_{32}*x_{43}+x_{21}*x_{42}+x_{31}*x_{43}+x_{41}),
      ideal(x_{32}*x_{41}+x_{31}*x_{42},x_{31}*x_{43}+x_{41},x_{32}*x_{43}+x_{42}),
      ideal(x_{32}*x_{41}+x_{31}*x_{42},x_{31}*x_{43}+x_{41},x_{32}*x_{43}+x_{42},x_{21
      }*x_{42}+x_{41},x_{21}*x_{32}+x_{31}),
      ideal(x_{31},x_{21},x_{41},x_{32}*x_{43}+x_{42}),
      ideal(x_{42},x_{41},x_{31},x_{21},x_{43}),
      ideal(x_{43},x_{42},x_{41},x_{32},x_{31},x_{21}),
      ideal(x_{42},x_{41},x_{32},x_{31},x_{21}),
      ideal(x_{42},x_{43},x_{41},x_{21}*x_{32}+x_{31}),
      ideal(x_{43},x_{42},x_{41},x_{31},x_{32}), ideal(x_{42},x_{31},x_{32},x_{41}),
      ideal(x_{31},x_{41},x_{32}*x_{43}+x_{42}), ideal(x_{41},x_{31},x_{42},x_{43}),
      ideal(x_{42},x_{41},x_{43}),
      ideal(x_{41},x_{21}*x_{32}*x_{43}+x_{21}*x_{42}+x_{31}*x_{43}),
      ideal(x_{41},x_{42},x_{21}*x_{32}+x_{31}), ideal(x_{42},x_{41},x_{31},x_{21}),
      ideal(x_{41},x_{31},x_{21}),
      ideal(x_{21}*x_{32}+x_{31},x_{32}*x_{41}+x_{31}*x_{42},x_{21}*x_{42}+x_{41}),
      ideal x_{41}, ideal(x_{41},x_{42}), ideal(x_{42},x_{41},x_{31}),
      ideal(x_{41},x_{31}), ideal(x_{32}*x_{41}+x_{31}*x_{42})}
assert(CompatibleIdeals==answer)
///
