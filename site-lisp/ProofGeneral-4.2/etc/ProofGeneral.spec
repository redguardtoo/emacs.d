Summary:	Proof General, Emacs interface for Proof Assistants
Name:		ProofGeneral
Version:	4.2
Release:	1
Group:		Text Editors/Integrated Development Environments (IDE)
License:	GPL
Url:		http://proofgeneral.inf.ed.ac.uk/
Packager:	David Aspinall <David.Aspinall@ed.ac.uk>
Source:		http://proofgeneral.inf.ed.ac.uk/ProofGeneral-%{version}.tgz
BuildRoot:	/tmp/ProofGeneral-root
BuildRequires:  emacs
PreReq:		/sbin/install-info
Prefixes:	/usr/share/emacs /usr/bin /usr/share/info
BuildArchitectures: noarch

%description
Proof General is a generic Emacs interface for proof assistants,
suitable for use by pacifists and Emacs militants alike.
It is supplied ready-customized for LEGO, Coq, and Isabelle.
You can adapt Proof General to other proof assistants if you know a
little bit of Emacs Lisp.

To use Proof General, use the command `proofgeneral', which launches
Emacs with Proof General loaded.

%changelog
* Fri May  4 2001 David Aspinall <David.Aspinall@ed.ac.uk> 
- Changelog in CVS now; official spec file developed with source.

%prep
%setup

%build
[ -n "${RPM_BUILD_ROOT}" ] && rm -rf ${RPM_BUILD_ROOT}

%install
mkdir -p ${RPM_BUILD_ROOT}/usr/share/emacs/ProofGeneral

# Clean out any .elc's that were in the tar file, and
# rebuild for the required emacs version.
make distclean

# Build packages and install
make install PREFIX=${RPM_BUILD_ROOT}/usr EMACS=emacs DEST_PREFIX=/usr

# Install docs too
make install-doc PREFIX=${RPM_BUILD_ROOT}/usr DEST_PREFIX=/usr DOCDIR=${RPM_BUILD_ROOT}%{_docdir}
rm -f ${RPM_BUILD_ROOT}/usr/share/info/dir
gzip ${RPM_BUILD_ROOT}/usr/share/info/*

# Rename READMEs in subdirs to avoid clashes
for f in */README; do mv $f $f.`dirname $f`; done

%clean
if [ "X" != "${RPM_BUILD_ROOT}X" ]; then
    rm -rf $RPM_BUILD_ROOT
fi

%post
/sbin/install-info /usr/share/info/ProofGeneral.info* /usr/share/info/dir
/sbin/install-info /usr/share/info/PG-adapting.info* /usr/share/info/dir
if [ -x /usr/bin/gtk-update-icon-cache ]; then
  gtk-update-icon-cache -q /usr/share/icons/hicolor
fi

%preun
/sbin/install-info --delete /usr/share/info/ProofGeneral.info* /usr/share/info/dir
/sbin/install-info --delete /usr/share/info/PG-adapting.info* /usr/share/info/dir

%postun
if [ -x /usr/bin/gtk-update-icon-cache ]; then
  gtk-update-icon-cache -q /usr/share/icons/hicolor
fi


%files
%defattr(-,root,root)
%{_bindir}/*
%doc %{_datadir}/man/man1/*
%doc %{_datadir}/info/*.info*
%doc %{_datadir}/doc/*
%{_datadir}/pixmaps/proofgeneral.png
%{_datadir}/icons/hicolor/*/proofgeneral.png
%{_datadir}/ProofGeneral/*
%{_datadir}/mime-info/proofgeneral.*
%{_datadir}/applications/proofgeneral.desktop
%{_datadir}/application-registry/proofgeneral.applications

