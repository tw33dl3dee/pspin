%%   Кафедра Математического моделирования
%%   Класс BPM2 - расширение классов BOOK и ARTICLE
%%   А.Н. Канатников
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


\NeedsTeXFormat{LaTeX2e}[2001/06/01]
\ProvidesClass{bpm2}[2002/02/02 LaTeX document class - extended BOOK]


\makeatletter

%%%    Команды установки собственных опций BPM2

\let\@Load@extraopt\relax
\def\@Use@Extraopt#1{\if@extraopt\@extraoptwarn{#1}\else
                        \edef\@filename{#1.clo}
                        \IfFileExists\@filename
                         {\def\@Load@extraopt{\expandafter\input\@filename}\@extraopttrue}
                         {\ClassWarning{BPM2}{Option \CurrentOption\space
                                              (file \@filename) is missing}}\fi}
%                         {\ClassWarning{BPM2}{Option \CurrentOption\space is missing}}\fi}
\newif\if@extraopt\@extraoptfalse
\def\@extraoptwarn#1{\ClassWarning{BPM2}{Option #1 contradict previous and ignored}}

%%%    Объявление собственных опций

\def\@ParentClass{book}
\def\@ParentClassNum{1}
\newif\if@Load@Myopt
\@Load@Myoptfalse
\newif\if@PageShift
\@PageShifttrue
\newcommand\BaseEncoding{LCY}
\def\@zachetname{zachet}
\newif\ifANSI
\ANSIfalse


\DeclareOption{article}{\def\@ParentClass{article}%
                        \def\@ParentClassNum{2}}
\DeclareOption{14pt}{\@Load@Myopttrue}
\DeclareOption{noshift}{\@PageShiftfalse}
\DeclareOption{ANSI}{\renewcommand\BaseEncoding{ANSI}\ANSItrue\def\@zachetname{zachetw}}
\DeclareOption{otchet}{\@Use@Extraopt{otchet}}
\DeclareOption{dissert}{\@Use@Extraopt{dissert}}
\DeclareOption{zachet}{\@Use@Extraopt{\@zachetname}}
\DeclareOption{ASCII}{\renewcommand\BaseEncoding{LCY}\ANSIfalse}
\DeclareOption*{\PassOptionsToClass{\CurrentOption}{\@ParentClass}}

%%%   Загрузка старшего класса

\ProcessOptions\relax

\if@Load@Myopt
   \let\@Save@def\ProcessOptions
   \def\ProcessOptions{\def\@ptsize{4}
           \let\ProcessOptions\@Save@def
           \let\@Save@def\relax\ProcessOptions}%
\fi


\LoadClass{\@ParentClass}



%%%    Если есть неиспользованные опции (неверные), сообщаем

\ifx\@unusedoptionlist\@empty \else
      \ClassWarningNoLine{bpm2}{There are unused Options: \@unusedoptionlist}\fi

%%%    Загрузка otchet - dissert - zachet

\AtEndOfClass{\@Load@extraopt}
\if@PageShift
  \AtBeginDocument{%
       \advance\oddsidemargin by -1in
       \advance\evensidemargin by -1in
       \advance\topmargin by -1in
                    }%
\fi


%%%    Шрифты AMSTeX

\RequirePackage{amssymb,amsbsy}


\long\def\hidden#1\endhidden{}




%   Для различения версий TEXa

\newif\ifmiktex
\miktextrue
\newif\ifpdftex
\@ifundefined{pdfoutput}{\pdftexfalse}{\ifnum1=\pdfoutput\pdftextrue\else\pdftexfalse\fi}
%\ifpdftex
%  \@ifundefined{pdfmapfile}{}{\pdfmapfile{+ttfonts.map}}
%\fi


%%%     Подключение шрифтов 

\def\UseBaseFont#1#2{%
      \input{#1enc.def}%
      \input{#1#2.fd}%
      \input{#1cmr.fd}%
      \DeclareFontSubstitution{#1}{#2}{m}{n}%
      \renewcommand\encodingdefault{#1}
      \renewcommand\familydefault{#2}%
      \renewcommand\rmdefault{#2}%
      \renewcommand\bfdefault{bx}%
      \renewcommand\itdefault{it}%
      \renewcommand\sfdefault{xcmss}%
      \renewcommand\sldefault{sl}%
      \def\sl{\fontfamily{xcmr}\fontshape{sl}\selectfont}%
              }%

% \UseBaseFont{\BaseEncoding}{cm}

% \DeclareMathAlphabet{\Cal}{U}{eus}{m}{n}


% %%%  Для использования кириллицы в именах функций и по команде \rm

% \DeclareSymbolFont{operators}      {\BaseEncoding}{xcmr}{m}{n}
% \SetSymbolFont{operators}    {bold}{\BaseEncoding}{xcmr}{bx}{n}
% \DeclareSymbolFont{letters}        {\BaseEncoding}{xcmm}{m}{it}
% \SetSymbolFont{letters}      {bold}{\BaseEncoding}{xcmm}{b}{it}



% \def\eng{\fontencoding{OT1}\fontfamily{cmr}%
%          \fontseries{m}\fontshape{n}\selectfont}


% \input omscmr.fd
% \input umsa.fd
% \input umsb.fd


%%%  Cимвол транспонирования в разных кодировках

\ifANSI
  \def\TMid{т}
\else
  \def\TMid{в}
\fi

%%        переносы в разных кодировках

\ifANSI
  \let\l@vrussian\l@ruswin
\else
  \let\l@vrussian\l@rusdos
\fi
\newcommand\changelanguage[1]{\expandafter\language\@nameuse{l@#1}}



%    Для проверки параметров на пустоту

\def\ifempty#1{\def\@tempa{#1}\ifx\@tempa\@empty}

%    Восстановление счетчиков

\def\resetcounter#1{\setcounter{#1}{0}}


%% Команда центрирования для многострочных заголовков

\def\raggedcenter@{\leftskip\z@ plus.4\hsize \rightskip\leftskip
 \parfillskip\z@ \parindent\z@ \spaceskip.5em \xspaceskip.7em\relax
 \pretolerance9999\tolerance9999 \exhyphenpenalty\@M\relax
 \hyphenpenalty\@M \let\\\linebreak}


%%   -------------------------------------------------
%%   Аналог команды @startsection, но с центрированием
%%   -------------------------------------------------

\def\@startctsection#1#2#3#4#5#6{\if@noskipsec \leavevmode \fi
   \par \@tempskipa #4\relax
   \@afterindenttrue
   \ifdim \@tempskipa <\z@ \@tempskipa -\@tempskipa \@afterindentfalse\fi
   \if@nobreak \everypar{}\else
     \addpenalty{\@secpenalty}\addvspace{\@tempskipa}\fi
     \@ifstar
     {\@sctsect{#3}{#4}{#5}{#6}}
     {\@threarg{\@ctsect{#1}{#2}{#3}{#4}{#5}{#6}}}}
\long\def\@threarg#1{\@ifnextchar [{\@nthrearg{#1}}{\@xthrearg{#1}}}
\long\def\@xthrearg#1#2{#1[{#2}][{#2}]{#2}}
\long\def\@nthrearg#1[#2]{\@ifnextchar [{#1[#2]}{#1[#2][#2]}}

%\long\def\@dblarg#1{\@ifnextchar[{#1}{\@xdblarg{#1}}}
%\long\def\@xdblarg#1#2{#1[{#2}]{#2}}

\def\@ctsect#1#2#3#4#5#6[#7][#8]#9{%
   \ifnum #2>\c@secnumdepth
     \let\@svsec\@empty
   \else
     \refscstepcounter{#1}\def\@svsec{\@makectsecthead{#1}\hskip #3}%
   \fi
   \@tempskipa #5\relax
   \ifdim \@tempskipa>\z@
     \begingroup
       \raggedcenter@ #6\relax\@svsec #9\par
     \endgroup
     \csname #1mark\endcsname{#8}%
     \addcontentsline{toc}{#1}%
        {\ifnum #2>\c@secnumdepth
         \else
           \protect\numberline
              {\hbox to 0pt{\hss
               \csname conthd#1\endcsname}\csname the#1\endcsname.}%
         \fi
         #7}%
   \else
     \def\@svsechd{%
        #6\hskip #3\relax  %% \relax added 2 May 90
        \@makectsecthead{#1}~#9\csname#1@dot\endcsname
        \csname #1mark\endcsname{#8}%
        \addcontentsline{toc}{#1}
           {\ifnum #2>\c@secnumdepth \else
              \protect\numberline{\csname the#1\endcsname.}
            \fi
            #7}%
        }
   \fi
   \@xsect{#5}}

\def\@@nsection#1#2#3-{\if@noskipsec \leavevmode \fi
   \par \@tempskipa #1\relax
   \@afterindenttrue
   \ifdim \@tempskipa <\z@ \@tempskipa -\@tempskipa \@afterindentfalse\fi
   \if@nobreak \everypar{}\else
    \addpenalty{\@secpenalty}\addvspace\@tempskipa\fi
    \@threarg{\@nsection{#1}{#2}{#3}}}
    
\def\@nsection#1#2#3[#4][#5]#6{\relax
     \@tempskipa #2\relax
     \ifdim \@tempskipa>\z@
        \begingroup
          \raggedcenter@ #3 #6\par
        \endgroup
     \else
        \def\@svsechd{#3\hskip\parindent#6\section@dot}%
     \fi
     \markright{#4}\relax
     \addcontentsline{toc}{section}{\protect\numberline{}#5}%
     \@xsect{#2}}

\def\@sctsect#1#2#3#4#5{\@tempskipa #3\relax
   \ifdim \@tempskipa>\z@
     \begingroup
         \interlinepenalty\@M \raggedcenter@ #4\hskip #1\relax #5\par
     \endgroup
   \else 
     \def\@svsechd{#4\hskip #1\relax #5\section@dot}%
   \fi
   \@xsect{#3}}


\def\@xsect#1{\@tempskipa #1\relax
      \ifdim \@tempskipa>\z@
       \par \nobreak
       \vskip \@tempskipa
       \@afterheading
    \else \global\@nobreakfalse \global\@noskipsectrue
       \everypar{\if@noskipsec \global\@noskipsecfalse
                   \clubpenalty\@M \hskip -\parindent
                   \begingroup \@svsechd \endgroup \unskip
                   \hskip -#1\relax  % relax added 14 Jan 91
                  \else \clubpenalty \@clubpenalty
                    \everypar{}\fi}\fi\ignorespaces}

\def\@makectsecthead#1{\csname head#1\endcsname
                  \csname the#1\endcsname.}
\def\section@dot{}

\def\secdelim#1{\def\@secdelimamount{#1}\gdef\@secdelim{\@secdelimamount}}
\secdelim{0.3em}


\def\CenteringSection{%
    \def\section{\@ifnextchar -{\@@nsection{\secsepbefore}{\secsepafter}%
                 \reset@font\sectionfont}{\@startctsection
                {section}{1}{\@secdelim}%
                {\secsepbefore}{\secsepafter}{\reset@font\sectionfont}}}%
    \gdef\headsection{}\gdef\conthdsection{}%
    \def\secsepbefore{3.5ex plus 1ex minus .2ex}%
    \def\secsepafter{2.3ex plus.2ex}%
             }



\def\refscstepcounter#1{\stepcounter{#1}\let\@tempa\protect
    \def\protect{\noexpand\protect\noexpand}%
    \edef\@currentlabel{\csname p@#1\endcsname
                    \csname conthd#1\endcsname
                    \csname the#1\endcsname}%
    \let\protect\@tempa}



%             Перечень общего назначения
\newcounter{sdi}
\newif\if@sdi@restore
\def\sdi{\@ifstar{\@sdi@restorefalse\@zsdi}{\@sdi@restoretrue\@zsdi}}
\def\@zsdi{\@ifnextchar[{\@psdi}{\@psdi[--]}}
\def\endsdi{\end{@sdi}\edef\@childsdi{\arabic{sdi}}}
\def\@psdi[#1]{\begin{@sdi}{#1}}
\newenvironment{@sdi}[1]
    {\edef\@parentsdi{\arabic{sdi}}%
     \if@sdi@restore\resetcounter{sdi}\else\setcounter{sdi}{\@childsdi}\fi
     \edef\@childsdi{0}%
     \@ifundefined{if@skiphyperref}{\relax}{\@skiphyperreftrue}%
     \topsep=2pt plus 1pt\itemsep=0pt
     \def\item{\@ifnextchar [{\@item}{\@item[#1]}}%
     \def\@item[##1]{\ifempty{##1}\let\@tempa\@zerosdi\fi
                     \refstepcounter{sdi}\par\addvspace\itemsep\indent
                     \hbox{\ignorespaces\@tempa\@itemadd\space}\ignorespaces}%
     \@usersdi
     \par\addvspace\topsep}
    {\par\vskip\topsep\setcounter{sdi}{\@parentsdi}\global\let\@itemadd\relax}
\let\@usersdi\relax
\def\usersdi#1{\def\@usersdi{#1{}\global\let\@usersdi\relax}\ignorespaces}
\def\itemadd#1{\def\@itemadd{#1}\ignorespaces}
\let\@itemadd\relax
\newcommand\@zerosdi[1]{\ignorespaces}

\def\@ctrexceed{\@latex@error{Counter is out of range}\@ehb}
\ifANSI
  \def\ralph#1{\ifcase #1\@ctrexceed\or
        а\or б\or в\or г\or д\or е\or ж\or з\or и\or к\or
        л\or м\or н\or о\or п\or р\or с\or т\or у\or ф\or
        х\or ц\or ч\or ш\or щ\or э\or ю\or я\else
        \@ctrexceed\fi}
\else
  \def\ralph#1{\ifcase #1\@ctrexceed\or
         \or Ў\or ў\or Ј\or ¤\or Ґ\or ¦\or §\or Ё\or Є\or
        «\or ¬\or ­\or ®\or Ї\or а\or б\or в\or г\or д\or
        е\or ж\or з\or и\or й\or н\or о\or п\else
        \@ctrexceed\fi}
\fi
\def\Ralph#1{\ifnum0=\value{#1}\@ctrexceed
        \else\ifnum28<\value{#1}\@ctrexceed
        \else\MakeUppercase{\ralph{#1}}\fi\fi}



%%%   Модификация параметров списков \@listi-\@listiii
%%%   добавлением в конец специальной команды \@userpar
\def\@change@itemlists{%
     \let\@tempa\@listi\edef\@listi{\@tempa\@userpar}%
     \let\@listI\@listi
     \let\@tempa\@listii\edef\@listii{\@tempa\@userpar}%
     \let\@tempa\@listiii\edef\@listiii{\@tempa\@userpar}%
     \let\@tempa\@openbib@code\edef\@openbib@code{\@tempa\@userpar}%
     \let\@change@itemlists\relax}
\def\userpar#1{\@change@itemlists
       \def\@userpar{#1\global\let\@userpar\relax}\ignorespaces}
\let\@userpar\relax



%%     Адаптация к Latex2e шрифтовых команд

\def\bi{\ifmmode\let\@next\boldsymbol
        \else\def\@next{\bfseries\itshape\mathversion{bold}}\fi\@next}
\def\@checkbi#1#2{}{}
\def\@setbi#1#2#3#4{}
\def\elvrm{\fontsize{11pt}{\baselineskip}\selectfont}
\def\Bbb{\mathbb}
\def\newfont#1#2{}
\let\@addfontinfo\newfont


%%%       Большие ограничители в стилях 10, 11 и 12 пунктов
\ifcase\@ptsize
   \or
     \def\big#1{{\hbox{\normalsize$\left#1\vbox to9.3\p@{}\right.\n@space$}}}
     \def\Big#1{{\hbox{\normalsize$\left#1\vbox to12.6\p@{}\right.\n@space$}}}
     \def\bigg#1{{\hbox{\normalsize$\left#1\vbox to15.9\p@{}\right.\n@space$}}}
     \def\Bigg#1{{\hbox{\normalsize$\left#1\vbox to19.2\p@{}\right.\n@space$}}}
   \or
     \def\big#1{{\hbox{\normalsize$\left #1\vbox to10.2pt{}\right.\n@space $}}}%
     \def\Big#1{{\hbox{\normalsize$\left #1\vbox to13.8pt{}\right.\n@space $}}}%
     \def\bigg#1{{\hbox{\normalsize$\left #1\vbox to17.4pt{}\right.\n@space $}}}%
     \def\Bigg#1{{\hbox{\normalsize$\left #1\vbox to21pt{}\right.\n@space $}}}%
   \or
   \or
     \def\big#1{{\hbox{\normalsize$\left #1\vbox to12.5pt{}\right.\n@space $}}}%
     \def\Big#1{{\hbox{\normalsize$\left #1\vbox to16.2pt{}\right.\n@space $}}}%
     \def\bigg#1{{\hbox{\normalsize$\left #1\vbox to20.3pt{}\right.\n@space $}}}%
     \def\Bigg#1{{\hbox{\normalsize$\left #1\vbox to24.5pt{}\right.\n@space $}}}%
\fi
%     Большое тире для п/ж курсива
\def\bfdash{\vbox{\hrule height 0.5pt depth0pt width1em\vskip0.55ex}}


\def\mparleft{\@mparswitchfalse\reversemarginpar}


%%          Нумерация страниц

\newcommand{\pageno}[1]{\setcounter{page}{#1}}
\newcommand{\chapterno}[1]{\setcounter{chapter}{#1}\addtocounter{chapter}{-1}}



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%        Обеспечение рисунков
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%     Механизм расширения по умолчанию и размещения по умолчанию

\def\@ParseFilename#1.#2;{\def\@CurrFilename{#1}\def\@CurrFileext{#2}}
\def\@AddFileext#1#2{\@ParseFilename#1.;\ifx\@CurrFileext\@empty
                    \def\@CurrFile{#1.#2}\else\def\@CurrFile{#1}\fi}
\def\@SetCurrfileSpec#1{\@AddFileext{#1}{\@DefaultPicext}%
                        \ifx\@DefaultPath\@empty
                            \def\@CurrFileSpec{\@CurrFile}\else
                            \def\@CurrFileSpec{\@DefaultPath/\@CurrFile}\fi}
\def\@PicSpecial#1#2{\edef\@SpecBody{{em:graph \@CurrFileSpec,#1,#2}}%
                \let\@CurrFileSpec\relax
                \expandafter\special\@SpecBody\relax}%
\def\UsePDFPic{\def\@PicSpecial##1##2{%
                      \pdfximage width##1 {\@CurrFileSpec}%
                      \let\@CurrFileSpec\relax
                      \pdfrefximage\pdflastximage}}


\def\DefaultPicExt#1{\def\@DefaultPicext{#1}}
\def\DefaultPath#1{\def\@DefaultPath{#1}}
\DefaultPicExt{BMP}
\DefaultPath{}


%%             Рисунки в боксах

%            Параметры:
%              1 - ширина;
%              2 - высота;
%              3 - имя файла рисунка
%              4 - имя метки для ссылок (figbox)
%                  или подрисуночный текст (picbox)

%%   Команды масштабирования

\def\@Graphscalefactor{1}
\newif\if@permscale\@permscalefalse
\newcommand\ScaleGraph{\@ifstar{\@permscaletrue\@ScaleGraph}
                               {\@permscalefalse\@ScaleGraph}}
\newcommand\@ScaleGraph[1]{\gdef\@Graphscalefactor{#1}\ignorespaces}
\def\showScale{\show\@Graphscalefactor}
%%  Команда отмены масштабирования рисунков (только для Yap)
\newcommand\OffScaleGraph{%
   \ifpdftex
   \else
      \def\@Graphscalefactor{1}
      \renewcommand\@ScaleGraph[1]{\@permscalefalse\ignorespaces}
      \def\@PicSpecial##1##2{\edef\@SpecBody{{em:graph \@CurrFileSpec}}%
                \let\@CurrFileSpec\relax
                \expandafter\special\@SpecBody\relax}%
   \fi}



%%%   Базовая команда размещения рисунка

\def\Grdunit#1{\def\@GrdU{#1}}
\Grdunit{pt}
%%  #1 ширина, #2 высота, #3 глубина (входит в высоту), #4 имя файла
\def\@gGraph#1#2#3#4{%
            \@tempdima=#1\relax
            \@tempdima=\@Graphscalefactor\@tempdima\relax
            \edef\@Graphwidth{\the\@tempdima}%
            \@tempdima=#2\@tempdima=\@Graphscalefactor\@tempdima
            \edef\@Graphheight{\the\@tempdima}%
            \if@permscale\else\gdef\@Graphscalefactor{1}\fi
            \setbox\@tempboxa
            \vbox to 0pt{\hsize=\@Graphwidth\offinterlineskip
            \hbox to \@Graphwidth{\@SetCurrfileSpec{#4}%
                        \@PicSpecial{\@Graphwidth}{\@Graphheight}\hfil}%
            \vss}%
            \@tempdima=-#3\advance\@tempdima by \@Graphheight
            \ht\@tempboxa=\@tempdima\dp\@tempboxa=#3
            \box\@tempboxa}

\def\Graph#1#2#3#4{\@addfigfile{graph}{#4}%
                   \@gGraph{#1}{#2}{#3}{#4}}


\def\picbox#1#2#3#4{\@addfigfile{picbox}{#3}%
                    \vbox{\@tempdima=#1\relax
                          \@tempdima=\@Graphscalefactor\@tempdima
                          \hsize=\@tempdima\offinterlineskip
                          \hbox{\@gGraph{#1}{#2}{\@Grdepth}{#3}}%
                          \ifempty{#4}
                          \else
                             \vskip\@picboxsep
                             \centering\captionfont\leavevmode\vphantom{b}#4%
                          \fi}}
\def\setGrdepth#1{\def\@Grdepth{#1\gdef\@Grdepth{\Grdepth}}\ignorespaces}
\def\@Grdepth{0pt}

\def\figbox#1#2#3#4{\@ifnextchar[
                      {\@figbox{#1}{#2}{#3}{#4}}%
                      {\@figbox{#1}{#2}{#3}{#4}[]}}
\def\@figbox#1#2#3#4[#5]{\@addfigfile{figbox}{#3}%
               \vbox{\@tempdima=#1\relax
                     \@tempdima=\@Graphscalefactor\@tempdima
                     \hsize=\@tempdima
                     \edef\@saveinterlineskip{\lineskip\the\lineskip
                                             \lineskiplimit\the\lineskiplimit}%
                     \offinterlineskip
                     \hbox{\@gGraph{#1}{#2}{0pt}{#3}}%
                     \vskip\@captionsep
                     \figcap[#5]{#4}}}
\let\@saveinterlineskip\relax


%%%     Подписи к рисункам

\def\figcap{\@ifnextchar[{\@figcap}{\@figcap[]}}
\def\@figcap[#1]#2{\vbox{\@figcollect\@saveinterlineskip
                   \def\@captype{figure}\relax
                   \ifempty{#1}\@caption@dotfalse\else\@caption@dottrue\fi
                   \caption{#1}\label{#2}}}
\newif\if@caption@dot

\long\def\@makecaption#1#2{%
  \if@caption@dot
     \def\@tempb{{#1.}\space}%
  \else
     \def\@tempb{{#1}}%
  \fi
  \sbox\@tempboxa{\captionfont\@tempb#2}%
  \ifdim \wd\@tempboxa >\hsize
     {\captionfont\@tempb#2\par}%
  \else
    \global \@minipagefalse
    \hb@xt@\hsize{\hfil\box\@tempboxa\hfil}%
  \fi}

\newcommand\captionfont{\fontsize{9pt}{10pt}\fontshape{n}\fontseries{m}\selectfont}
\def\captionsep#1{\def\@captionsep{#1}\ignorespaces}
\def\picboxsep#1{\def\@picboxsep{#1}\ignorespaces}
\captionsep{10\p@}
\let\@picboxsep\@captionsep




%      Система подсчета рисунков и таблиц
%        В преамбулу поместить команду \figcollect, \tabcollect
%        за последней главой - команду \demofig, \demotab
%        В протокол будет выведено количество рисунков.


\let\@figcollect\relax
\def\demofig{\ifANSI
                \typeout{Учет рисунков не ведется}%
             \else
                \typeout{“зҐв аЁбг­Є®ў ­Ґ ўҐ¤Ґвбп}
             \fi}
\def\figcollect{\newcounter{allfig}%
        \def\@figcollect{\addtocounter{allfig}1}%
            \ifANSI
              \def\demofig{\typeout{Встречено рисунков: \arabic{allfig}}}%
            \else
              \def\demofig{\typeout{‚бваҐзҐ­® аЁбг­Є®ў: \arabic{allfig}}}%
            \fi}

\let\@tabcollect\relax
\def\demotab{\ifANSI
                \typeout{Учет таблиц не ведется}%
             \else
                \typeout{“зҐв в Ў«Ёж ­Ґ ўҐ¤Ґвбп}%
             \fi}
\def\tabcollect{\newcounter{alltab}%
       \def\@tabcollect{\addtocounter{alltab}1}%
            \ifANSI
               \def\demotab{\typeout{Встречено таблиц: \arabic{alltab}}}%
            \else
               \def\demotab{\typeout{‚бваҐзҐ­® в Ў«Ёж: \arabic{alltab}}}%
            \fi}


%%%  Для врезки рисунков в абзац (рисунок как линейка нулевой ширины)

\def\dfb#1{\ifvmode \let\@tempa=\relax \else \let\@tempa=\vadjust\fi
           \@tempa{\vbox to 0pt{#1\vss}}}


%%%     Распечатка списка рисунков

\def\printfigfiles{\newwrite\tf@lfn
     \immediate\openout\tf@lfn\jobname.lfn\relax
     \def\@addfigfile##1##2{\begingroup\@fileswtrue
                \@addlistline{lfn}{##1}{##2}\endgroup}}
\def\@addfigfile#1#2{}
\def\@addlistline#1#2#3{\if@filesw \begingroup
    \let\label\@gobble \let\index\@gobble \let\glossary\@gobble
    \def\protect##1{\string##1}%
    \edef\@tempa{\write\tf@lfn
    %                 {‘ва. \thepage, д ©« #3, вЁЇ #2}}%
                      {\protect\contentsline{#2}{#3}{\thepage}}}%
     \@tempa
     \if@nobreak \ifvmode\nobreak\fi\fi\endgroup\fi}


%%%      Разрывы абзацев и т.п.
\def\wbreak{{\parfillskip=0pt\par\noindent}\hangafter=0}
\def\vbreak{\vskip-\lastskip
            \ifdim\prevdepth>-1000pt\vskip-\prevdepth\fi
            \pagebreak}
\newcommand\crskip[1]{\noalign{\vskip-\lastskip\nobreak\vskip#1pt}}
            

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%            Таблицы в боксах
%      Использование: \tabbox{метка}{текст таблицы}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\def\tabbox#1#2{\@tabcollect\refstepcounter{table}\label{#1}%
                \setbox\@tempboxa\hbox{#2}%
                \parbox[t]{\wd\@tempboxa}{%
                \hbox to \wd\@tempboxa{\hfil
                      \fnum@table}%
                \vspace{\tabcapsep}
                \unhbox\@tempboxa}}
\def\tabcapsep{6\p@}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%      Модификация \marginpar 
%%%     (для подавления сообщений о смещении)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\def\@addmarginpar{\@next\@marbox\@currlist{\@cons\@freelist\@marbox
    \@cons\@freelist\@currbox}\@latexbug\@tempcnta\@ne
    \if@twocolumn
        \if@firstcolumn \@tempcnta\m@ne \fi
    \else
      \if@mparswitch
         \ifodd\c@page \else\@tempcnta\m@ne \fi
      \fi
      \if@reversemargin \@tempcnta -\@tempcnta \fi
    \fi
    \ifnum\@tempcnta <\z@  \global\setbox\@marbox\box\@currbox \fi
    \@tempdima\@mparbottom
    \advance\@tempdima -\@pageht
    \advance\@tempdima\ht\@marbox
    \ifdim\@tempdima >\z@
       \@curr@warning@no@line{Marginpar on page \thepage\space moved}%
    \else
      \@tempdima\z@
    \fi
    \global\@mparbottom\@pageht
    \global\advance\@mparbottom\@tempdima
    \global\advance\@mparbottom\dp\@marbox
    \global\advance\@mparbottom\marginparpush
    \advance\@tempdima -\ht\@marbox
    \global\setbox \@marbox
                   \vbox {\vskip \@tempdima
                          \box \@marbox}%
    \global \ht\@marbox \z@
    \global \dp\@marbox \z@
    \kern -\@pagedp
    \nointerlineskip
    \hb@xt@\columnwidth
      {\ifnum \@tempcnta >\z@
          \hskip\columnwidth \hskip\marginparsep
       \else
          \hskip -\marginparsep \hskip -\marginparwidth
       \fi
       \box\@marbox \hss}%
    \nointerlineskip
    \hbox{\vrule \@height\z@ \@width\z@ \@depth\@pagedp}}
\newinsert \@kludgeins
\global\dimen\@kludgeins \maxdimen
\global\count\@kludgeins 1000
\gdef \enlargethispage {%
   \@ifstar
     {%
      \@enlargepage{\hbox{\kern\p@}}}%
     {%
      \@enlargepage\@empty}%
}
\let\@curr@warning@no@line\@latex@warning@no@line
\def\SuppressMarginWarning{\def\@curr@warning@no@line##1{}}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%       Переопределение \nofiles для подавления
%%%       "паразитного" вывода
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\def\nofiles{%
  \@fileswfalse
  \typeout{No auxiliary output files.^^J}%
  \long\def\protected@write##1##2##3{%
    %\write\m@ne{}%
    \if@nobreak\ifvmode\nobreak\fi\fi}%
  \let\makeindex\relax
  \let\makeglossary\relax}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%       "Заметки на полях" (в конце макета для своб. страниц)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\def\forNotes#1{{\large\bf
                \@tempcnta=#1\loop\ifnum\@tempcnta>0
                \advance\@tempcnta by -1
                \newpage\thispagestyle{empty}%
                \hbox to \hsize{\hfil „«п § ¬Ґв®Є\hfil}\repeat
                \newpage}}



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%               Расширенная математика
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%%              \multline
%--------------------------------------------------------------
%             Исправление \stepcounter
\def\m@stepcounter#1{\global\advance\csname c@#1\endcsname \@ne
    \let\@elt\@stpelt\csname cl@#1\endcsname}
%               collectenvbody
\newtoks\@envbody
\def\addto@envbody#1{\@envbody\expandafter{\the\@envbody#1}}
\def\collect@body#1{%
  \@envbody{}%
  \def\process@envbody{%
    \expandafter#1\expandafter{\the\@envbody}}%
  \expandafter\let\csname\@currenvir\endcsname\collect@@body
  \csname\@currenvir\endcsname}
\def\collect@@body#1\end#2{%
  \def\@tempa{#2}%
  \ifx\@tempa\@currenvir
    \addto@envbody{#1}%
    \expandafter\edef\csname\@currenvir\endcsname
      {\noexpand\process@envbody\noexpand\end{\@tempa}}%
  \else
    \addto@envbody{#1\end{#2}}%
  \fi
  \csname\@currenvir\endcsname}
%          Сокращения
\def\setbox@ne{\setbox\@ne}
\def\setboxz@h{\setbox\z@\hbox}
\def\wd@ne{\wd\@ne}
\def\wdz@{\wd\z@}
\def\boxz@{\box\z@}
\def\DN@{\def\next@}
%           Разрыв строк
\def\@multcr{\@ifstar{\global\@eqpen\@M \@ymultcr}%
            {\global\@eqpen\interdisplaylinepenalty \@ymultcr}}
\def\@ymultcr{\@ifnextchar [{\@xmultcr}{\@xmultcr[\z@]}}
\def\@xmultcr[#1]{\cr\noalign{\penalty-\@eqpen
      \vskip #1\relax}}
%           Новые регистры для \multline
\newbox\mtagbox@
\newdimen\rtwidth@
\newdimen\mwidth@
\newdimen\multlinegap
\newdimen\multlinetaggap@
\multlinegap10pt
\multlinetaggap@10pt
%
\def\multline{%
 \ifmmode\@badmath\DN@{\let\endmultline\relax\@gobble}%
 \else $$\DN@{\collect@body\rmultline@@}\fi
 \@eqnswtrue\let\@currentlabel\theequation
 \m@stepcounter{equation}\next@}%
\@namedef{multline*}{%
 \ifmmode\@badmath\DN@{\@namedef{endmultline*}{}\@gobble}%
 \else $$\DN@{\collect@body\rmultline@@}\fi
 \@eqnswfalse \let\@currentlabel\@empty
 \next@}
\def\rmultline@@#1{%
    \rmmeasure@{#1}%
    \setbox\mtagbox@\hbox{\if@eqnsw \@eqnnum\fi}%
    \dimen@\mwidth@\advance\dimen@\wd\mtagbox@
    \advance\dimen@\multlinetaggap@
    \ifdim\dimen@>\displaywidth\rtwidth@\z@\else\rtwidth@\wd\mtagbox@\fi
    \rmultline@@@#1}
\def\rmultline@@@{\displ@y
 \def\shoveright##1{##1\hfilneg\if@eqnsw\ifdim\rtwidth@>\z@
  \hskip\rtwidth@\hskip\multlinetaggap@\fi\else\hskip\multlinegap\fi}%
 \def\shoveleft##1{\setboxz@h{$\m@th\displaystyle{}##1$}%
   \setbox@ne\hbox{$\m@th\displaystyle##1$}%
   \hfilneg\hskip\multlinegap\hskip.5\wd@ne\hskip-.5\wdz@##1}%
 \halign\bgroup\let\\\@multcr
  \hbox to\displaywidth
  {\strut$\m@th\displaystyle\hfil{}##\hfil$}\crcr
 \hfilneg\hskip\multlinegap}
\def\rmmeasure@#1{%
 \def\shoveleft##1{##1}\def\shoveright##1{##1}%
 \setbox@ne\vbox{\let\\\@multcr\halign{\setboxz@h     %\firstchoice@false
  {$\m@th\@lign\displaystyle{}##$}\global\mwidth@\wdz@
  \crcr#1\crcr}}}
\def\endmultline{\rendmultline@\global\@ignoretrue}
\expandafter\let\csname endmultline*\endcsname=\endmultline
\def\rendmultline@{\if@eqnsw
 \ifdim\rtwidth@>\z@
  \hskip\multlinetaggap@\box\mtagbox@
 \else\llap{\vtop{\normalbaselines\null\hbox{\strut\box\mtagbox@}}}\fi
 \else\hskip\multlinegap\fi
 \hfilneg\crcr\egroup$$}
%
%               \aligned  и \cases
\def\aligned{\begin{@aligned}}\def\endaligned{\end{@aligned}}
\newenvironment{@aligned}{\null\,\vcenter \bgroup
          \def\vspace##1{\crcr\noalign{\vskip##1\relax }} \Let@
          \iffalse \else \openup \jot \fi
          \ialign \bgroup \hfil \strut $\m@th \displaystyle {##}$& $\m@th
                   \displaystyle {{}##}$\hfil \crcr }
           {\crcr\egroup\egroup }
\def\Let@{\relax \iffalse {\fi \let \\=\cr \iffalse }\fi }
\def\cases{\begin{@cases}}\def\endcases{\end{@cases}}
\newenvironment{@cases}{\left\{\vcenter\bgroup
          \def\vspace##1{\crcr\noalign{\vskip##1\relax }} \Let@
         \iffalse \else \openup \jot \fi
         \ialign\bgroup
         \hfil\strut$\displaystyle{##}\m@th$&$\displaystyle{{}##}\m@th$\hfil
        &\quad\hfil$\displaystyle{##}\m@th$&$\displaystyle{{}##}\m@th$\hfil\cr}
            {\crcr\egroup\egroup\right.}
%
%       Адаптивные ограничители формул
%       ограничители \( и \) добавляют пробел \eqnskip до и после
%       строчной формулы. При этом пробел до не ставится, если перед
%       формулой нет пробела, а пробел после выносится за знаки пунктуации.
%       Отмена пробела - пустая пара скобок {}
%
\def\({\ifvmode\leavevmode$\else
       \ifdim\lastskip>0pt\hskip\eqnskip$\else$\fi\fi}
\def\){$\@fixeqnskip}

\def\@fixeqnskip{\futurelet\@tempeqna\@ifeqnch}
\def\@ifeqnch{\ifx\@tempeqna\@sptoken
                  \def\@tempeqnb{\hskip\eqnskip{}}\else
                  \ifx\@tempeqna\bgroup\def\@tempeqnb{}\else
                  \@testsym{.,;)?"}{\@tempeqna}
                         {\def\@tempeqnb{\@xifeqnch}}
                         {\def\@tempeqnb{}}%
                  \fi\fi\@tempeqnb}

\def\@xifeqnch#1{#1\@fixeqnskip}
\def\eqnskip{0pt}

\def\@testsym#1#2#3#4{\edef\@temptsa{#1}\let\@temptsb#2%
                      \def\@temptse{#3}\def\@temptsf{#4}\@xtestsym}
\def\@xtestsym{\let\@nil\relax
               \expandafter\ifx\@temptsa\@nil\@nil
                                    \def\@temptsd{\@temptsf}\else
                \edef\@temptsc{\expandafter\@car\@temptsa\@nil}%
                \edef\@temptsa{\expandafter\@cdr\@temptsa\@nil}%
                \if\@temptsc\@temptsb\def\@temptsd{\@temptse}\else
                    \def\@temptsd{\@xtestsym}\fi\fi\@temptsd}

%  Команда \text из amsmath

\DeclareRobustCommand{\text}{%
  \ifmmode\expandafter\text@\else\expandafter\mbox\fi}
\let\nfss@text\text
\def\text@#1{{\mathchoice
  {\textdef@\displaystyle\f@size{#1}}%
  {\textdef@\textstyle\f@size{\firstchoice@false #1}}%
  {\textdef@\textstyle\sf@size{\firstchoice@false #1}}%
  {\textdef@\textstyle \ssf@size{\firstchoice@false #1}}%
  \check@mathfonts
  }%
}
\def\textdef@#1#2#3{\hbox{{%
                    \everymath{#1}%
                    \let\f@size#2\selectfont
                    #3}}}
\newif\iffirstchoice@
\firstchoice@true


%     Другие команды для формул

\let\mz\m@th     % подавление дополнительных пробелов вокруг формулы
\def\nbpr-{\nobreak\hskip0pt\hbox{-}\nobreak\hskip0pt}  %  неразрывный дефис
\def\nb{\protect\nbpr}    %  защищенный вариант
%     Восстановление возможных разрывов при наличии дефиса
\def\nf-{\nobreak\hskip0pt\discretionary{-}{}{-}\nobreak\hskip0pt}
%     Увеличение левой апроши у дефиса
\def\df-{\nobreak\hskip0.03em\discretionary{-}{}{-}\nobreak\hskip0em}
%     Смещение дефиса вправо (после буквы о)
\def\ofpr-{\nobreak\kern0.03em-\hskip-0.1em}
\def\of{\protect\ofpr}
\def\dsf.{\spacefactor=\the\sfcode`.\relax}
\def\nsf.{\spacefactor=1000}
\def\setdf#1#2{\left\{ #1 \colon\hskip2pt #2 \right\}}
\def\mapdf#1#2#3{#1 \colon\hskip2pt #2 \mhyph\to #3}
\def\IR#1#2{\ovl{#1,\,#2}}
\def\sfrac#1#2{\hbox{\footnotesize$\displaystyle\frac{#1}{#2}$}}
\def\varliminf{\mathop{\ul{\vrule height0pt depth.2ex width0pt
                           \hbox{\rm lim}}}}
\def\varlimsup{\mathop{\overline{\hbox{\rm lim}}}}
%      символ для операции "композиция" - уменьшенный \circ
\def\cps{\mathbin{\raise0.2ex\hbox{\footnotesize$\m@th{\circ}$}}}
%\newcommand\m@th{\mathsurround=\z@}
\def\mspacestretch#1{\thinmuskip=#1\thinmuskip\medmuskip=#1\medmuskip
                     \thickmuskip=#1\thickmuskip}
\def\mspsh#1#2#3{\thickmuskip=#1\thickmuskip
                         plus #2\thickmuskip
                        minus #3\thickmuskip
                 \medmuskip=#1\medmuskip
                       plus #2\medmuskip
                      minus #3\medmuskip
                 \thinmuskip=#1\thinmuskip
                        plus #2\thinmuskip
                       minus #3\thinmuskip    }
\let\msps\mspacestretch
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%%             Кавычки "лапки" и знак номера
%
\def\al{\leavevmode\vbox to 0pt{\hbox{"}\vss}\penalty10000\hskip0pt}
\def\ar{``}
\chardef\nomer=194
%
%%                 Заполнители в матрицах
%
\def\Dotline#1{\multispan{#1}\strut
   \cleaders\hbox{$\m@th \mkern5mu.\mkern4mu$}\hfill\kern\z@}
\def\dotline#1#2{\hbox to #1em{\hbox to #2em{\dotfill}\hss}}
%
%%%              Математические списки
%%       Обращение: \mlist{a;b;c...} (в фигурных скобках через
%%                                    запятую)
%%           Сопутствующие команды:
%%             \mlistright - Ограничитель слева
%%             \mlistright - Ограничитель справа
%%             \mlistdel   - Ограничитель между
%%             \vcoord{список} - координаты вектора
%%             \pcoord{список} - координаты точки
%%             \row{список} - матрица-строка
%%             \set{список} - запись множества перечислением
%%             \setsh{список} - то же, но с уменьшенными пробелами
%
\def\mlist#1{{\def\@mlist##1;{\ifx\relax##1\let\@next=\mlistright
                 \else\def\@next{\@curdelim##1\let\@curdelim=\mlistdel
                      \@mlist}\fi
                 \@next}\let\@curdelim=\mlistleft
                 \@mlist#1;\relax;}}
\def\mlistleft{\left\{}\def\mlistright{\right\}}\def\mlistdel{;}
\def\pcoord#1{{\def\mlistleft{\left(}\def\mlistright
               {\right)}\def\mlistdel{;\coordsp}\mlist{#1}}}
\def\vcoord#1{{\def\mlistleft{\left\{}\def\mlistright
               {\right\}}\def\mlistdel{;\coordsp}\mlist{#1}}}
\let\coordsp\relax
\newcommand\setsp{\hskip3pt}
\def\set#1{{\def\mlistleft{\left\{}\def\mlistright
          {\right\}}\def\mlistdel{,\setsp}\mlist{#1}} }
\def\setsh#1{{\def\mlistleft{\left\{}\def\mlistright
          {\right\}}\def\mlistdel{,}\mlist{#1}} }
\def\rowsp{\hskip3pt}
%\let\rowsp\relax
\newcommand{\row}[1]{{\def\mlistleft{\left(}\def\mlistright
               {\right)}\def\mlistdel{,\rowsp}\mlist{#1}}}

%%
%%        Знаки кратных интегралов
%%
\def\@intic{\mathchoice{\hskip.5em}{\hskip.4em}{\hskip.4em}{\hskip.4em}}
\def\@negintic{\mathchoice
 {\hskip-.5em}{\hskip-.4em}{\hskip-.4em}{\hskip-.4em}}
\def\@ointkern{\mathchoice{\mkern-20mu}{\mkern-15mu}{\mkern-15mu}{\mkern-15mu}}
\def\@oiskern{\mathchoice{\mkern-14mu}{\mkern-10mu}{\mkern-10mu}{\mkern-10mu}}
\def\@intkern{\mathchoice{\mkern-6mu}{\mkern-4mu}{\mkern-4mu}{\mkern-4mu}}
\def\@intdots{\mathchoice{\mathinner{\cdotp\cdotp\cdotp}}
 {{\cdotp}\mkern1.5mu{\cdotp}\mkern1.5mu{\cdotp}}
 {{\cdotp}\mkern1mu{\cdotp}\mkern1mu{\cdotp}}
 {{\cdotp}\mkern1mu{\cdotp}\mkern1mu{\cdotp}}}
\def\iint{\relax\futurelet\@nexti\@iint}
\def\@iint{\ifx\@nexti\limits
               \def\@@iint{\@negintic
                          \mathop{\@intic\int\@intkern\int}}%
            \else
            \def\@@iint{\mathop{\int\@intkern\intop}\nolimits}%
            \fi
            \@@iint}
\def\iiint{\relax\futurelet\@nexti\@iiint}
\def\@iiint{\ifx\@nexti\limits
               \def\@@tmpint{\@negintic
                          \mathop{\@intic\int\@intkern\int\@intkern\int}}%
            \else
            \def\@@tmpint{\mathop{\intop\@intkern
                                 \intop\@intkern\intop}\nolimits}%
            \fi
            \@@tmpint}
\def\oiint{\relax\futurelet\@nexti\@oiint}
\def\@oiint{\ifx\@nexti\limits
             \def\@@tmpint{\@negintic
                       \mathop{\@intic\subset\@ointkern
                               \int\@oiskern\int\@ointkern\supset}}%
              \else
              \def\@@tmpint{%
                       \mathop{\subset\@ointkern
                               \int\@oiskern\int\@ointkern\supset}}%
              \fi
              \@@tmpint}
\def\idotsint{\relax\futurelet\@nexti\@idint}
\def\@idint{\ifx\@nexti\limits
             \def\@@tmpint{\@negintic
                       \mathop{\@intic\int\@intdots\int}}%
              \else
              \def\@@tmpint{\mathop{\intop\@intdots\intop}\nolimits}%
              \fi
              \@@tmpint}




%%        Текст в разрядку. Обращение \looser{<число>}{текст}
%%        <число> - величина клея в em'ах между буквами.

\newcount\@oldcatcode
\def\looser{\@oldcatcode=\the\catcode` \catcode` =13\relax\@looser}
%\def\@looser#1#2{\bgroup
%     \def\loos@space{\kern #1em}%
%     \def\loos@next{\loos@text}%
%     \def\loos@text ##1{##1\loos@space\loos@next}%
%     \loos@text #2{\let\loos@next=\relax\catcode` =\the\@oldcatcode}%
%     \egroup}
\def\@looser#1#2{\def\loos@space{\kern #1em}%
     \def\loos@text ##1{##1\loos@space\noexpand\loos@text}%
     \loos@text #2{\kern-#1em\let\loos@text=\relax
                   \catcode` =\the\@oldcatcode}\relax}

%%%         Альтернативный вариант текста в разрядку

\def\aloos#1#2{\def\alos@space{\kern#1em}%
     \@tempskipa=1em\edef\alos@exspace{\alosecoef\@tempskipa}%
     \def\alos@text##1{##1\alos@space\noexpand\alos@ask}%
     \alos@ask#2{\unskip\kern-#1em\let\alos@text=\relax}\relax}
\def\alosecoef{0.2}
\def\alos@ask{\futurelet\alos@next\alos@alz}
\def\alos@alz{\if\alos@next\space\penalty0{ }\hskip\alos@exspace\fi\alos@text}


%    для отображения защищенных команд
\def\showRobcom#1{\expandafter\show\csname
      \expandafter\@gobble\string#1 \endcsname}


%%        Особые математические символы

\newcommand\mathsymbol[2]{\@tempcnta=#2\advance\@tempcnta by 256
                          #1{\mathchar\@tempcnta}}
\let\msym\mathsymbol
\let\bifam\boldsymbol


%%     Изменения вида греческих букв

\let\@tempa\theta\let\theta\vartheta\let\vartheta\@tempa
\let\@tempa\phi\let\phi\varphi\let\varphi\@tempa
\let\@tempa\epsilon\let\epsilon\varepsilon\let\varepsilon\@tempa
\let\eps\epsilon



%%
%%       Сокращения и прочее
%%
\def\ovl{\overline}
\def\ul{\underline}
\let\ro\rho
\let\les\leqslant\let\ges\geqslant
\def\[{\begin{equation}}\def\]{\end{equation}}
\def\={\mhyph=}
\newcommand{\mhyph}[1]{#1\penalty10000\discretionary{}{\hbox{$#1\mz$}}{}}
\newcommand{\pl}{+\discretionary{}{\hbox{${}+\mz$}}{}}
\newcommand{\mi}{-\discretionary{}{\hbox{${}-\mz$}}{}}
\newcommand{\diez}{{\rm \#}}
\newcommand{\ft}{\footnotesize}
\newcommand{\rowex}{\def\arraystretch{1.7}}
\newcommand\0[1]{\mathop{\hbox{$#1$}}\limits^\circ}
\def\T{{\vbox{\vskip2pt\hbox{\ft\rm \TMid}\vskip2pt}}}  %  индекс транспонирования
\def\amb{\discretionary{}{}{}}
\let\ds\displaystyle
\let\ts\textstyle
\def\vct#1{\left(\begin{array}{@{\:}c@{\:}} #1 \end{array}\right)}
%              Обозначение производной (в виде $a^{\dr5})
\def\dr#1{\ifcase #1 {(0)} \or\prime \or{\prime\prime} \or
           {\prime\prime\prime} \else{\edef\up{{\romannumeral #1}}%
                \scriptscriptstyle\rm
                \expandafter\uppercase\up}\fi}
%
%      Команды для верстки
%
\newcommand{\upto}{{\kern1pt--\kern1pt}}
\newcommand{\brto}[1]{\vbox to 0cm{\vss\hbox to 0cm{$\left\{\vrule
            height #1\baselineskip depth #1\baselineskip width0pt
           \right.$\hss}\vss}}
\newcommand\htcut[1]{\setbox0=\hbox{#1}\ht0=0pt \box0{}}
\newcommand\dpcut[1]{\setbox0=\hbox{#1}\dp0=0pt \box0{}}
\newcommand\hquality[1]{\pretolerance=#1\tolerance=#1\hbadness=#1}
%%% €§¬Ґ­Ґ­ЁҐ Ї а ¬Ґва®ў а §¬Ґа®ў
\newcommand\change[4]{#1=#2#1 plus #3#1 minus #4#1}
\newcommand\changebase[3]{\change\baselineskip{#1}{#2}{#3}}
\newcommand\changedisplay[3]{%
        \change\abovedisplayskip{#1}{#2}{#3}%
        \change\abovedisplayshortskip{#1}{#2}{#3}%
        \change\belowdisplayskip{#1}{#2}{#3}}
\newcommand\changecom[4]{\@tempskipa=#1
          \change\@tempskipa{#2}{#3}{#4}%
          \edef#1{\the\@tempskipa}}
\newcommand\showskip[1]{\@tempskipa=#1\showthe\@tempskipa}

\newcommand{\lb}{\protect\\}
\newcommand{\Lb}{\penalty-10000}
\def\vdis#1{\lineskip=#1pt\lineskiplimit=#1pt}
\newcommand\usup[2]{\vrule height#1ex depth#2ex width0em}
\newcommand\usupw[2]{\vrule height#1ex depth#2ex width0.3pt}

\def\dividecounter#1#2{\divide \value{#1} by #2}
%%%   запятая как разделитель типа точки (без дополнительного пробела)   
\def\ordcomma{%
      \@tempcnta=\the\mathcode`,
      \@tempcntb=\@tempcnta
      \divide\@tempcntb by 4096 \multiply\@tempcntb by 4096
      \@tempcntb=-\@tempcntb \advance\@tempcnta by \@tempcntb
      \mathcode`,=\@tempcnta
             }




%%      Обрамление доказательств

\def\proof{\relax\ifmmode \blacktriangleleft
           \mskip 36mu plus 0mu minus 18mu
           \else
           \par\addvspace\medskipamount\noindent$\blacktriangleleft$\ \fi}
\def\endproof{\ifmmode \mskip 36mu plus 0mu
                        minus 18mu\blacktriangleright
              \else
              \unskip~$\blacktriangleright$\par
              \vskip\medskipamount\fi}

%%%       Ссылки на рисунки и таблицы


\ifANSI
  \newcommand\figrefid{рис}
  \newcommand\Figrefid{Рис}
  \newcommand\Tabrefid{Табл}
  \newcommand\tabrefid{табл}
  \newcommand\Tabremid{Тбл}
  \newcommand\tabremid{тбл}
\else
  \newcommand\figrefid{аЁб}
  \newcommand\Figrefid{ђЁб}
  \newcommand\Tabrefid{’ Ў«}
  \newcommand\tabrefid{в Ў«}
  \newcommand\Tabremid{’Ў«}
  \newcommand\tabremid{вЎ«}
\fi

\def\Nfig{\@fig{\Figrefid}}
\def\nfig{\@ifstar{\ref}{\@fig{\figrefid}}}
\def\Ffig{\@figm{\Figrefid}}
\def\ffig{\@ifstar{\@figr{\figrefid}}{\@figm{\figrefid}}}
\def\figmark#1#2{\marginpar{\hbox{\fbox{\ft\bf#1\@figdot\ref{#2}}\hss}}}
\def\@fig#1#2{#1\@figdot~\ref{#2}}
\def\@figm#1#2{\@fig{#1}{#2}\figmark{#1}{#2}}
\def\@figr#1#2{\ref{#2}\figmark{#1}{#2}}
\def\@figdot{.}

\def\@tabm#1#2{\@fig{#1}{#2}\figmark{\tabremid}{#2}}
\def\ftab{\@ifstar{\@figr{\tabremid}}{\@tabm{\tabrefid}}}
\def\Ftab{\@ifstar{\@figr{\Tabremid}}{\@tabm{\Tabrefid}}}
\def\ntab{\@ifstar{\ref}{\tabrefid.~\ref}}
\newcommand{\Ntab}[1]{\Tabrefid.~\ref{#1}}
%%
%%              Имена меток на полях
%%
\newcommand{\rem}[1]{\marginpar{\small\raggedright\sffamily #1}}
\def\showlabels{\openin\@inputcheck showlbl.sty
       \ifeof\@inputcheck\typeout
       {ЌҐв д ©«  showlbl.sty, ®ЇжЁп showlabels ЁЈ­®аЁагҐвбп}\else
       \closein\@inputcheck\relax
       %\typeout{ЋЇжЁп showlabels ўЄ«озҐ­ }%
       \input showlbl.sty\fi
       }
%     Переопределение шрифтов под стиль 12pt
\def\twlfont{\openin\@inputcheck twlfont.sty
       \ifeof\@inputcheck\typeout
       {ЌҐв д ©«  twlfont.sty, ®ЇжЁп twlfont ЁЈ­®аЁагҐвбп}\else
       \closein\@inputcheck\relax
       %\typeout{ЋЇжЁп showlabels ўЄ«озҐ­ }%
       \input twlfont.sty\fi
       }

%%%       Окружение для титульных страниц

\def\gentitle{\begin{@booktitle}}
\def\endtitle{\end{@booktitle}\pageround{\textheight}}
\newenvironment{@booktitle}
    {\newpage\lineskip1pt\lineskiplimit0pt
     \ifcase \@ptsize \relax
    \or
      \twlfont
      \pagestyle{empty}%
    \or
      \twlfont
      \pagestyle{empty}%
      \topskip=0pt
      \headsep=0pt
      \headheight=0pt
      \textheight=172mm\advance\textheight by -\headheight
%                    \advance\textheight by -\topskip
                     \advance\textheight by -\headsep
      \pageround{\textheight}%
      \textwidth=112mm
      \hsize=\textwidth
      \advance\hoffset by 20mm
      \advance\voffset by 20mm
    \fi}
    {\pagebreak}



%%%    Вариантная загрузка в зависимости от базового стиля

\ifcase\@ParentClassNum \or \usepackage{bpm_bk} \fi


\makeatother

\endinput

