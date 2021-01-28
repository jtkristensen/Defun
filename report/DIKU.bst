% Released $Date: 2012-09-28 23:02:19 $
%
% Comments can be sent to jyrki@diku.dk
%
% Development history
%
% Tue Dec  1 01:35:17 CET 2009 Added webbook -Bo
% Thu May 15 20:13:28 CEST 2008 Now techrept accepts an editor -Jyrki
% Sun Oct 21 14:00:26 MEST 2007 Case change in the thesis type omitted -Jyrki
% 5.6.2007 The format of note was changed; outputs the text inside parentheses.
% 4.2.2005 Now author names are output in roman, not in small caps \Jyrki
% 27.1.2004  Organization added to book \Jyrki
% 10.10.2002 Now site is printed by techreport. \Søren Jyrki
% 29.8.2002 Now unpublished outputs the title in roman. \Jyrki
% 15.8.2002 I corrected an error in the formatting of "von" names. \Jyrki
% 12.10.2001 Jeppe wanted that editor is removed inproceedings. He also asked
%            whether url should be provided by other entries than website and
%            webdocument. However, nothing was done for the latter. \Jyrki
% 18.4.2001 Year added to website. \Jyrki
% 17.4.2001 Article, techreport and thesis titles in lower case letters. \Jyrki
% 26.9.2000 Use url-package to maim url-addresses. \Jyrki
% 3.7.2000 Testing and correcting some small errors. Jyrki Katajainen
% 30.6.2000 Minor revisions in series and inproceedings
%           and a major cleanup of the code. Jyrki Katajainen
% 19.6.2000 New types: webdocument and website. Lars Yde
% 15.6.2000 Changes in bvolume. Jyrki Katajainen
% 7.6.2000 Changes in article. Jyrki Katajainen
%
% Adaption by Tomi Pasanen
%	OF
% ACM Transactions bibliography style (24-Jan-88 version)
% filename "acm.bst"
%	AND OF
% American Mathematical Society bibliography style 13-Oct-1994 version 1.2beta
% filename "amsplain.bst"

% Status: Bibliography entries 
% booklet, 
% inbook,
% misc,
% have not been tested.
% Cross-references have never been used.

% BibtTeX is  a primitive stack engine created by Oren Patashnik. A style 
% file like this translates the bibliography entries mentioned in an aux-file 
% and described in a bib-file to a sequence of tokens (name, title, journal, 
% etc.) in the LaTeX-format to a bbl-file. This program considers the entries
% one at a time, generates the tokens for each entry, and the mode tells
% which separator is outputted _before_ each token. The default separator is
% blank (" "); other separators are comma (", "), colon (": "), and period
% (". "). Knowing this it should be relatively easy to modify the output
% corresponding to any bibliography entry if necessary.

% This style file knows also non-standard entries webdocument and website,
% and field site which gives a Web address.
%
% webdocument
% Required fields: (author or editor) or (organization and key), title, 
% site, year; Optional field: note
%
% website
% Required fields: editor or organization (or both), key, title, site, year.
% Optional field: note
%
% Observe that inproceedings an address refers to the address of the
% publisher, not to the location where the confrerence was held.

ENTRY
  { address
    author
    booktitle
    chapter
    edition
    editor
    howpublished
    institution
    journal
    key
    month
    note
    number
    organization
    pages
    publisher
    school
    series
    site
    title
    type
    volume
    year
  }
  {}
  { label }

INTEGERS { output.state blank comma colon period }

FUNCTION {init.state.consts}
{ #0 'blank  :=
  #1 'comma :=
  #2 'colon :=
  #3 'period :=
}

STRINGS { s t }

FUNCTION {output.nonnull}
{ 's :=
  output.state comma =
    { ", " * write$ }
    { output.state period =
        { add.period$ write$
	      newline$
	    }
        { output.state blank =
            { " " * write$ }
            { ": " * write$ }
	      if$
	    }
      if$
    }
  if$
  s
}

FUNCTION {output}
{ duplicate$ empty$
    'pop$
    'output.nonnull
  if$
}

FUNCTION {output.check}
{ 't :=
  duplicate$ empty$
    { pop$ "empty " t * " in " * cite$ * warning$ }
    'output.nonnull
  if$
}

FUNCTION {output.bibitem}
{ newline$
  "\bibitem{" write$
  cite$ write$
  "}" write$
  newline$
  ""
  blank 'output.state :=
}

FUNCTION {blank.mode}
{ blank 'output.state :=
}

FUNCTION {comma.mode}
{ comma 'output.state :=
}

FUNCTION {colon.mode}
{ colon 'output.state :=
}

FUNCTION {period.mode}
{ period 'output.state :=
}

FUNCTION {output.note}
{ note empty$
    'skip$
    { note output }
  if$
}

FUNCTION {full.stop}
{
  add.period$
  write$
  newline$
}

FUNCTION {no.full.stop}
{
  write$
  newline$
}

FUNCTION {not}
{   { #0 }
    { #1 }
  if$
}

FUNCTION {and}
{   'skip$
    { pop$ #0 }
  if$
}

FUNCTION {or}
{   { pop$ #1 }
    'skip$
  if$
}

FUNCTION {field.or.null}
{ duplicate$ empty$
    { pop$ "" }
    'skip$
  if$
}

FUNCTION {emphasize}
{ duplicate$ empty$
    { pop$ "" }
    { "\emph{" swap$ * "}" * }
  if$
}

FUNCTION {scapify}
{ duplicate$ empty$
    { pop$ "" }
    { "\textsc{" swap$ * "}" * }
  if$
}

INTEGERS { nameptr namesleft numnames }


%FUNCTION {format.names}
%{ 's :=
%  #1 'nameptr :=
%  s num.names$ 'numnames :=
%  numnames 'namesleft :=
%    { namesleft #0 > }
%%    { s nameptr "{vv~}{ll}{, jj}{, f.}" format.name$ 't :=
%     { s nameptr "{f.~}{vv~}{ll}{, jj}" format.name$ 't :=
%      nameptr #1 >
%	{ namesleft #1 >
%	    { ", " * t * }
%	    { t "others" =
%		{ ", et~al." * }
%%		{ ", and " * t * }
%		{ " and " * t * }
%	      if$
%	    }
%	  if$
%	}
%	't
%      if$
%      nameptr #1 + 'nameptr :=
%      namesleft #1 - 'namesleft :=
%    }
%  while$
%}

FUNCTION {format.names}
{ 's :=
  #1 'nameptr :=
  s num.names$ 'numnames :=
  numnames 'namesleft :=
    { namesleft #0 > }
%    { s nameptr "{ff~}{vv~}{ll}{, jj}" format.name$ 't :=
    { s nameptr "{f.~}{vv~}{ll}{, jj}" format.name$ 't :=
%     { s nameptr "{f{.\,}.~}{vv~}{ll}{, jj}" format.name$ 't :=
      nameptr #1 >
        { namesleft #1 >
            { ", " * t * }
            { numnames #2 >
                { "," * }
                'skip$
              if$
              t "others" =
                { " et~al." * }
                { " and " * t * }
              if$
            }
          if$
        }
        't
      if$
      nameptr #1 + 'nameptr :=
      namesleft #1 - 'namesleft :=
    }
  while$
}


% For names inside entries (e.g., editors of an "In ...");
% this is exactly ABBRV.BST's `format.names' function.
FUNCTION {format.innames}
{ 's :=
  #1 'nameptr :=
  s num.names$ 'numnames :=
  numnames 'namesleft :=
    { namesleft #0 > }
    { s nameptr "{f.~}{vv~}{ll}{, jj}" format.name$ 't :=
      nameptr #1 >
	{ namesleft #1 >
	    { ", " * t * }
	    { numnames #2 >
		{ "," * }
		'skip$
	      if$
	      t "others" =
		{ " et~al." * }
		{ " and " * t * }
	      if$
	    }
	  if$
	}
	't
      if$
      nameptr #1 + 'nameptr :=
      namesleft #1 - 'namesleft :=
    }
  while$
}

FUNCTION {format.authors}
{ author empty$
    { "" }
    { author format.names }
  if$
}

FUNCTION {format.editors}
{ editor empty$
    { "" }
    { editor format.names 
      editor num.names$ #1 >
        { " (Editors)" * }
        { " (Editor)" * }
      if$
    }
  if$
}

FUNCTION {format.title}
{ title empty$
    { "" }
    { title emphasize }
  if$
}

FUNCTION {lower.title}
{ title empty$
    { "" }
    { title "t" change.case$ }
  if$
}

FUNCTION {format.booktitle}
{ booktitle empty$
    { "" }
    { booktitle emphasize }
  if$
}

FUNCTION {n.dashify}
{ 't :=
  ""
    { t empty$ not }
    { t #1 #1 substring$ "-" =
	{ t #1 #2 substring$ "--" = not
	    { "--" *
	      t #2 global.max$ substring$ 't :=
	    }
	    {   { t #1 #1 substring$ "-" = }
		{ "-" *
		  t #2 global.max$ substring$ 't :=
		}
	      while$
	    }
	  if$
	}
	{ t #1 #1 substring$ *
	  t #2 global.max$ substring$ 't :=
	}
      if$
    }
  while$
}

FUNCTION {format.date}
{ year empty$
    { month empty$
	    'skip$
	    { "there's a month but no year in " cite$ * warning$ }
      if$
    ""
    }
    { " (" year * ")" * }
  if$
}

FUNCTION {tie.or.space.connect}
{ duplicate$ text.length$ #3 <
    { "~" }
    { " " }
  if$
  swap$ * *
}

FUNCTION {either.or.check}
{ empty$
    'pop$
    { "can't use both " swap$ * " fields in " * cite$ * warning$ }
  if$
}

FUNCTION {format.series}
{ series empty$
	{ "" }
	{ series emphasize
      volume empty$
       'skip$
       { " \textbf{" * volume * "}" * }
      if$
     "volume and number" number either.or.check
    }
  if$
}

FUNCTION {format.edition}
{ edition empty$
    { "" }
    { output.state comma =
	{ edition "l" change.case$ "~Edition" * }
	{ edition "t" change.case$ "~Edition" * }
      if$
    }
  if$
}

FUNCTION {format.pages}
{ pages empty$
    { "" }
    { pages n.dashify }
  if$
}

INTEGERS { multiresult }

FUNCTION {multi.page.check}
{ 't :=
  #0 'multiresult :=
    { multiresult not
      t empty$ not
      and
    }
    { t #1 #1 substring$
      duplicate$ "-" =
      swap$ duplicate$ "," =
      swap$ "+" =
      or or
	{ #1 'multiresult := }
	{ t #2 global.max$ substring$ 't := }
      if$
    }
  while$
  multiresult
}

FUNCTION {format.pp.pages}
{ pages empty$
    { "" }
    { pages multi.page.check
        { "pp.~" pages n.dashify * }
        { "p.~" pages * }
      if$
    }
  if$
}

FUNCTION {format.chapter.pages}
{ chapter empty$
    'format.pages
    { type empty$
        { "Chapter~" chapter * }
        { type "t" change.case$ chapter tie.or.space.connect }
      if$
      pages empty$
        'skip$
        { ", " * format.pages * }
      if$
    }
  if$
}

FUNCTION {empty.misc.check}
{ author empty$ title empty$ howpublished empty$
  month empty$ year empty$ note empty$
  and and and and and
  key empty$ not and
    { "all relevant fields are empty in " cite$ * warning$ }
    'skip$
  if$
}

FUNCTION {format.thesis.type}
{ type empty$
    'skip$
    { pop$
      type
    }
  if$
}

FUNCTION {format.tr.number}
{ type empty$
    { "Technical Report" }
    'type
  if$
  number empty$
    { "t" change.case$ }
    { " \textbf{" * number * "}" * }
  if$
}

FUNCTION {format.article.crossref}
{ key empty$
    { journal empty$
	{ "need key or journal for " cite$ * " to crossref " * crossref *
	  warning$
	  ""
	}
	{ "in \emph{" journal * "}" * }
      if$
    }
    { "in " key * }
  if$
  " \cite{" * crossref * "}" *
}

FUNCTION {format.crossref.editor}
{ editor #1 "{vv~}{ll}" format.name$
  editor num.names$ duplicate$
  #2 >
    { pop$ " et~al." * }
    { #2 <
	'skip$
	{ editor #2 "{ff }{vv }{ll}{ jj}" format.name$ "others" =
	    { " et~al." * }
	    { " and " * editor #2 "{vv~}{ll}" format.name$ * }
	  if$
	}
      if$
    }
  if$
}

FUNCTION {format.book.crossref}
{ volume empty$
    { "empty volume in " cite$ * "'s crossref of " * crossref * warning$
      "in "
    }
    { " Vol.~\textbf{" volume * "}" *
      " of " *
    }
  if$
  editor empty$
  editor field.or.null author field.or.null =
  or
    { key empty$
	{ series empty$
	    { "need editor, key, or series for " cite$ * " to crossref " *
	      crossref * warning$
	      "" *
	    }
%	    { " \emph{" * series * "}" * }
	    { " \emph{" * series * "}" * }
	  if$
	}
	{ key * }
      if$
    }
    { format.crossref.editor * }
  if$
  " \cite{" * crossref * "}" *
}

FUNCTION {format.incoll.inproc.crossref}
{ editor empty$
  editor field.or.null author field.or.null =
  or
    { key empty$
	{ booktitle empty$
	    { "need editor, key, or booktitle for " cite$ * " to crossref " *
	      crossref * warning$
	      ""
	    }
	    { "in \emph{" booktitle * "}" * }
	  if$
	}
	{ "in " key * }
      if$
    }
    { "in " format.crossref.editor * }
  if$
  " \cite{" * crossref * "}" *
}  

FUNCTION {format.site}
{ 
"\url{" site * "}" *
}
   	  
FUNCTION {article}
{ output.bibitem
  format.authors "author" output.check
  comma.mode
  lower.title "title" output.check
  crossref missing$
    { journal empty$
        { "empty journal in " cite$ * warning$
          ""
        }
        { journal emphasize
          volume empty$
	        'skip$
	        { " \textbf{" * volume * "}" * }
          if$
          number empty$
	        'skip$
            { ", " * number * }
          if$
        }
      if$
      output
      blank.mode
      format.date "year" output.check
      comma.mode
      format.pages output
    }
    { format.article.crossref output.nonnull
      format.pages output
    }
  if$
  period.mode
  output.note
  note missing$
    {full.stop}
    {no.full.stop}
  if$
}

FUNCTION {book}
{ output.bibitem
  author empty$
    { editor empty$
        { organization empty$
            { "author, editor, or organization required in " cite$ * warning$ }
            { organization output }
          if$
        }
        { format.editors output }
      if$
    }
    { format.authors output.nonnull
      crossref missing$
	    { "author and editor" editor either.or.check }
	    'skip$
      if$
    }
  if$
  comma.mode
  format.title "title" output.check
  format.series output
  format.edition output
  crossref missing$
    { publisher "publisher" output.check
      address output
    }
    { format.book.crossref output.nonnull
    }
  if$
  blank.mode
  format.date "year" output.check
  period.mode
  output.note
  note missing$
    {full.stop}
    {no.full.stop}
  if$
}

FUNCTION {booklet}
{ output.bibitem
  format.authors output
  comma.mode
  format.title "title" output.check
  howpublished output
  address output
  blank.mode
  format.date output
  period.mode
  output.note
  note missing$
    {full.stop}
    {no.full.stop}
  if$
}

FUNCTION {inbook}
{ output.bibitem
  author empty$
    { format.editors "author and editor" output.check }
    { format.authors output.nonnull
      crossref missing$
        { "author and editor" editor either.or.check }
        'skip$
      if$
    }
  if$
  comma.mode
  format.title "title" output.check
  author empty$
    'skip$
    { format.editors output }
  if$
  format.series output
  format.edition output
  crossref missing$
    { publisher "publisher" output.check
      address output
    }
    { format.book.crossref output.nonnull }
  if$
  blank.mode
  format.date "year" output.check
  format.chapter.pages "chapter and pages" output.check
  period.mode
  output.note
  note missing$
    {full.stop}
    {no.full.stop}
  if$
}

FUNCTION {incollection}
{ output.bibitem
  format.authors "author" output.check
  comma.mode
  lower.title "title" output.check
  crossref missing$
    { format.booktitle "booktitle" output.check
%      format.editors output
      format.series output      
      format.edition output
      publisher "publisher" output.check
      address output
      blank.mode
      format.date "year" output.check
    }
    { format.incoll.inproc.crossref output.nonnull }
  if$
  comma.mode
  format.chapter.pages output
  period.mode
  output.note
  note missing$
    {full.stop}
    {no.full.stop}
  if$
}

FUNCTION {inproceedings}
{ output.bibitem
  format.authors "author" output.check
  comma.mode
  lower.title "title" output.check
  crossref missing$
    { format.booktitle "booktitle" output.check
%      format.editors output
      format.series output
      publisher output
      address output
      blank.mode 
      format.date "year" output.check
    }
    { format.incoll.inproc.crossref output.nonnull }
  if$
  comma.mode
  format.pages output
  period.mode
  output.note
  note missing$
    {full.stop}
    {no.full.stop}
  if$
}

FUNCTION {conference} { inproceedings }

FUNCTION {manual}
{ output.bibitem
  author empty$
    { organization output }
    { format.authors output.nonnull }
  if$
  comma.mode
  format.title "title" output.check
  format.edition output
  author empty$
    'skip$
    { organization output }
  if$
  address output
  blank.mode
  format.date output
  period.mode
  output.note
  note missing$
    {full.stop}
    {no.full.stop}
  if$
}

FUNCTION {mastersthesis}
{ output.bibitem
  format.authors "author" output.check
  comma.mode
  lower.title "title" output.check
  "M.\,Sc.\ Thesis" format.thesis.type output.nonnull
  school "school" output.check
  address output
  blank.mode
  format.date "year" output.check
  period.mode
  output.note
  note missing$
    {full.stop}
    {no.full.stop}
  if$
}

FUNCTION {misc}
{ output.bibitem
  format.authors output
  comma.mode
  format.title output
  howpublished output
  blank.mode
  format.date output
  period.mode
  output.note
  note missing$
    {full.stop}
    {no.full.stop}
  if$
  empty.misc.check
}

FUNCTION {phdthesis}
{ output.bibitem
  format.authors "author" output.check
  comma.mode
  lower.title "title" output.check
  "Ph.\,D.\ Thesis" format.thesis.type output.nonnull
  school "school" output.check
  address output
  blank.mode
  format.date "year" output.check
  period.mode
  output.note
  note missing$
    {full.stop}
    {no.full.stop}
  if$
}

FUNCTION {proceedings}
{ output.bibitem
  editor empty$
    { organization output }
    { format.editors output.nonnull }
  if$
  comma.mode
  format.title "title" output.check
  format.editors output
  format.series output
  publisher empty$
    { organization output }
    { publisher output }
  if$
  address output
  blank.mode
  format.date "year" output.check
  period.mode
  output.note
  note missing$
    {full.stop}
    {no.full.stop}
  if$
}

FUNCTION {techreport}
{ output.bibitem
  author empty$
    { format.editors "editor" output.check }
    { format.authors output.nonnull }
  if$
  comma.mode
  lower.title "title" output.check
  format.tr.number output.nonnull
  institution "institution" output.check
  address output
  blank.mode
  format.date "year" output.check
  period.mode
  site empty$
    'skip$
    {    period.mode 
     "Available at " output
    blank.mode
    format.site output
    period.mode}
  if$
  output.note
  note missing$
    {full.stop}
    {no.full.stop}
  if$
}

FUNCTION {unpublished}
{ output.bibitem
  format.authors "author" output.check
  comma.mode
  lower.title "title" output.check
  note empty$
    {note "note" output.check}
    {output.note}
  if$
  blank.mode
  format.date output
  full.stop
}

FUNCTION {format.webauthors}
{ author empty$
    { "" }
    { author }
  if$
}
FUNCTION {webdocument}
{ output.bibitem
  author empty$
    { editor empty$
        { organization empty$
            { "author, editor, or organization required in " cite$ * warning$ }
            { organization output }
          if$
        }
        { format.editors output }
      if$
    }
    { format.authors output }
  if$  
  comma.mode 
  lower.title "title" output.check
  "Worldwide Web Document" output
  blank.mode
  format.date "year" output.check
  period.mode
  "Available at " output
  blank.mode
  format.site "site" output.check
  output.note
  note missing$
    {full.stop}
    {no.full.stop}
  if$
}
FUNCTION {webbook}
{ output.bibitem
  author empty$
    { editor empty$
        { organization empty$
            { "author, editor, or organization required in " cite$ * warning$ }
            { organization output }
          if$
        }
        { format.editors output }
      if$
    }
    { format.authors output }
  if$  
  comma.mode 
  format.title "title" output.check
  "Worldwide Web Document" output
  blank.mode
  format.date "year" output.check
  period.mode
  "Available at " output
  blank.mode
  format.site "site" output.check
  output.note
  note missing$
    {full.stop}
    {no.full.stop}
  if$
}


FUNCTION {website}
{ output.bibitem
  author empty$
    { editor empty$
        { organization empty$
            { "author, editor, or organization required in " cite$ * warning$ }
            { organization output }
          if$
        }
        { format.editors output }
      if$
    }
    { format.authors output }
  if$  
  comma.mode
  lower.title "title" output.check
  "Website accessible at " output
  blank.mode
  format.site "site" output.check
  format.date "year" output.check
  output.note
  note missing$
    {full.stop}
    {no.full.stop}
  if$
}

FUNCTION {default.type} { misc }

MACRO {jan} {"Jan."}

MACRO {feb} {"Feb."}

MACRO {mar} {"Mar."}

MACRO {apr} {"Apr."}

MACRO {may} {"May"}

MACRO {jun} {"June"}

MACRO {jul} {"July"}

MACRO {aug} {"Aug."}

MACRO {sep} {"Sept."}

MACRO {oct} {"Oct."}

MACRO {nov} {"Nov."}

MACRO {dec} {"Dec."}

MACRO {acmcs} {"ACM Comput. Surv."}

MACRO {acta} {"Acta Inf."}

MACRO {cacm} {"Commun. ACM"}

MACRO {ibmjrd} {"IBM J. Res. Dev."}

MACRO {ibmsj} {"IBM Syst.~J."}

MACRO {ieeese} {"IEEE Trans. Softw. Eng."}

MACRO {ieeetc} {"IEEE Trans. Comput."}

MACRO {ieeetcad}
 {"IEEE Trans. Comput.-Aided Design Integrated Circuits"}

MACRO {ipl} {"Inf. Process. Lett."}

MACRO {jacm} {"J.~ACM"}

MACRO {jcss} {"J.~Comput. Syst. Sci."}

MACRO {scp} {"Sci. Comput. Programming"}

MACRO {sicomp} {"SIAM J. Comput."}

MACRO {tocs} {"ACM Trans. Comput. Syst."}

MACRO {tods} {"ACM Trans. Database Syst."}

MACRO {tog} {"ACM Trans. Gr."}

MACRO {toms} {"ACM Trans. Math. Softw."}

MACRO {toois} {"ACM Trans. Office Inf. Syst."}

MACRO {toplas} {"ACM Trans. Program. Lang. Syst."}

MACRO {tcs} {"Theoretical Comput. Sci."}

READ

FUNCTION {sortify}
{ purify$
  "l" change.case$
}

INTEGERS { len }

FUNCTION {chop.word}
{ 's :=
  'len :=
  s #1 len substring$ =
    { s len #1 + global.max$ substring$ }
    's
  if$
}

FUNCTION {sort.format.names}
{ 's :=
  #1 'nameptr :=
  ""
  s num.names$ 'numnames :=
  numnames 'namesleft :=
    { namesleft #0 > }
    { nameptr #1 >
	{ "   " * }
	'skip$
      if$
      s nameptr "{ll{ }}{  f{ }}{  jj{ }}" format.name$ 't :=
      nameptr numnames = t "others" = and
	{ "et al" * }
	{ t sortify * }
      if$
      nameptr #1 + 'nameptr :=
      namesleft #1 - 'namesleft :=
    }
  while$
}

FUNCTION {sort.format.title}
{ 't :=
  "A " #2
    "An " #3
      "The " #4 t chop.word
    chop.word
  chop.word
  sortify
  #1 global.max$ substring$
}

FUNCTION {author.sort}
{ author empty$
    { key empty$
	{ "to sort, need author or key in " cite$ * warning$
	  ""
	}
	{ key sortify }
      if$
    }
    { author sort.format.names }
  if$
}

FUNCTION {author.editor.sort}
{ author empty$
    { editor empty$
	{ key empty$
	    { "to sort, need author, editor, or key in " cite$ * warning$
	      ""
	    }
	    { key sortify }
	  if$
	}
	{ editor sort.format.names }
      if$
    }
    { author sort.format.names }
  if$
}

FUNCTION {author.organization.sort}
{ author empty$
    { organization empty$
	{ key empty$
	    { "to sort, need author, organization, or key in " cite$ * warning$
	      ""
	    }
	    { key sortify }
	  if$
	}
	{ "The " #4 organization chop.word sortify }
      if$
    }
    { author sort.format.names }
  if$
}

FUNCTION {editor.organization.sort}
{ editor empty$
    { organization empty$
	{ key empty$
	    { "to sort, need editor, organization, or key in " cite$ * warning$
	      ""
	    }
	    { key sortify }
	  if$
	}
	{ "The " #4 organization chop.word sortify }
      if$
    }
    { editor sort.format.names }
  if$
}

FUNCTION {presort}
{ type$ "book" =
  type$ "inbook" =
  or
    'author.editor.sort
    { type$ "proceedings" =
	'editor.organization.sort
	{ type$ "manual" =
	    'author.organization.sort
	    'author.editor.sort
	  if$
	}
      if$
    }
  if$
  "    "
  *
  year field.or.null sortify
  *
  "    "
  *
  title field.or.null
  sort.format.title
  *
  #1 entry.max$ substring$
  'sort.key$ :=
}

ITERATE {presort}

SORT

STRINGS { longest.label }

INTEGERS { number.label longest.label.width }

FUNCTION {initialize.longest.label}
{ "" 'longest.label :=
  #1 'number.label :=
  #0 'longest.label.width :=
}

FUNCTION {longest.label.pass}
{ number.label int.to.str$ 'label :=
  number.label #1 + 'number.label :=
  label width$ longest.label.width >
    { label 'longest.label :=
      label width$ 'longest.label.width :=
    }
    'skip$
  if$
}

EXECUTE {initialize.longest.label}

ITERATE {longest.label.pass}

FUNCTION {begin.bib}
{ preamble$ empty$
    'skip$
    { preamble$ write$ newline$ }
  if$
  "\begin{thebibliography}{"  longest.label  * "}" * write$ newline$
}

EXECUTE {begin.bib}

EXECUTE {init.state.consts}

ITERATE {call.type$}

FUNCTION {end.bib}
{ newline$
  "\end{thebibliography}" write$ newline$
}

EXECUTE {end.bib}
