#!/usr/bin/python
# coding:utf-8:

from email.MIMEMultipart import MIMEMultipart
from email.MIMEText import MIMEText
from email.MIMEImage import MIMEImage

import PIL.Image

import getpass
import smtplib
import subprocess
import time
import re
import os
import sys

def fail_conf_file():
    print
    print '! There should be a .pruf.conf file.'
    print '! Contents (three lines):'
    print '!    example@post.wordpress.com'
    print '!    example@gmail.com'
    print '!    blog_name                    (i.e. http://blog_name.wordpress.com)'
    print
    sys.exit(1)

def read_conf_file():
    if not os.path.exists('.pruf.conf'):
        fail_conf_file()
    f = file('.pruf.conf')
    to = f.readline()
    gmail_user = f.readline()
    blog_name = f.readline()
    f.close()
    if blog_name == '':
        fail_conf_file()
    to = to.strip(' \t\r\n')
    gmail_user = gmail_user.strip(' \t\r\n')
    blog_name = blog_name.strip(' \t\r\n')
    return to, gmail_user, blog_name

def resource_name(res_name, slug, i):
    if res_name == '':
        res_name = '%.2u' % (i,)
    return '%s_%s' % (slug.lower(), res_name.lower())

def wordpress_remove_external_attachments(slug, contents, attachment_sizes={}):
    _, _, blog_name = read_conf_file()
    year = time.strftime('%Y')
    month = time.strftime('%m')
    i = 0
    names = {}
    while True:
        i += 1
        m = re.search('[%][%]([^{]*)[{]([^%]*)[%][%][}]', contents)
        if m is None: break
        res_name = m.expand('\\1').strip(' \t\r\n')
        res = resource_name(res_name, slug, i)

        if res in names:
            print '!!! error: resource name "%s" is used twice' % (res,)
            sys.exit(1)
        names[res] = 1

        if res_name == '':
            alt = ''
        else:
            alt = ' alt="%s"' % (res_name,)
        size = attachment_sizes.get(res, 500)
        link = '<img src="http://%s.files.wordpress.com/%s/%s/%s.png?w=%s"%s>' % (blog_name, year, month, res, size, alt)
        contents = contents[:m.start()] + link + contents[m.end():]
    return contents

def make_img_from_formula(res, formula):
    tex = '''
\\documentclass{article}
\\usepackage{graphicx}
\\usepackage[active,tightpage]{preview}
\\usepackage{pstricks}
INCLUDES
\\begin{document}
\\begin{preview}
FORMULA
\\end{preview}
\\end{document}
'''
    tex = tex.replace('INCLUDES', latex_includes())
    tex = tex.replace('FORMULA', formula)
    os.system('rm -f media/%s.png' % (res,))
    os.system('rm -f _tmp*')
    f = file('_tmp.tex', 'w')
    f.write(tex)
    f.close()
    resol = 1000
    os.system('latex _tmp.tex') # >/dev/null 2>&1
    os.system('dvipng -D %i -bg Transparent -pp 1 _tmp.dvi' % (resol,)) # >/dev/null 2>&1

    img = PIL.Image.open('_tmp1.png')
    size = img.size[0] / 4 # width

    os.system('cp _tmp1.png media/%s.png' % (res,))
    os.system('rm -f _tmp*')
    return size

def make_attachments(slug, bare_contents):
    print 'making attachments...'
    attachments = {}
    _, _, blog_name = read_conf_file()
    year = time.strftime('%Y')
    month = time.strftime('%m')
    i = 0
    while True:
        i += 1
        m = re.search('[%][%]([^{]*)[{]([^%]*)[%][%][}]', bare_contents)
        if m is None: break
        res_name = m.expand('\\1').strip(' \t\r\n')
        res = resource_name(res_name, slug, i)
        formula = m.expand('\\2')
        size = make_img_from_formula(res, formula)
        bare_contents = bare_contents[m.end():]
        attachments[res] = size
    return attachments

def wordpress(slug, bare_contents, attachment_sizes={}):
    contents = bare_contents
    contents = contents.replace('\n\n', '<BR>')
    contents = contents.replace('\n', ' ')
    contents = contents.replace('<BR>', '\n\n')
    contents = re.sub('[$][$]([^$]*)[$][$]', r'<div style="text-align: center;">$\\displaystyle \1$</p>', contents)
    contents = re.sub('[$]([^$]*)[$]', '$latex \\1$', contents)
    contents = contents.replace(' < ', '&lt;')
    contents = contents.replace(' > ', '&gt;')
    contents = contents.replace("``", '"')
    contents = contents.replace("''", '"')
    contents = wordpress_remove_external_attachments(slug, contents, attachment_sizes)

    print 80 * '-'
    print contents
    print 80 * '-'
    return '[slug %s]' % (slug,) + contents

def wrap_latex(bare_contents, slug=None):
    if slug is not None:
        label_slug = '\\\\label{%s}' % (slug,)
    else:
        label_slug = ''
    contents = bare_contents
    contents = re.sub('[[]title ([^]]*)[]]', r"\n\\section{\1}%s\n" % (label_slug,), contents)
    #contents = re.sub('[[]category ([^]]*)[]]', r"\n\\noindent{\\bf \1}\n", contents)
    #contents = re.sub('[[]tags ([^]]*)[]]', r"\n\\noindent{\\em \1}\\vspace{10pt}\n", contents)
    contents = re.sub('[[](title|category|tags|end)[^]]*[]]', '', contents)
    contents = re.sub('\r', '\n', contents)
    contents = re.sub('\n[\n]+', '\n\n', contents)
    contents = re.sub('([^\n])\n([^\n])', r"\1 \2", contents)
    contents = re.sub('á', r"\'a", contents)
    contents = re.sub('é', r"\'e", contents)
    contents = re.sub('í', r"\'i", contents)
    contents = re.sub('ó', r"\'o", contents)
    contents = re.sub('ú', r"\'u", contents)
    contents = re.sub('Á', r"\'A", contents)
    contents = re.sub('É', r"\'E", contents)
    contents = re.sub('Í', r"\'I", contents)
    contents = re.sub('Ó', r"\'O", contents)
    contents = re.sub('Ú', r"\'U", contents)
    contents = re.sub('ü', r"\"u", contents)
    contents = re.sub('Ü', r"\"U", contents)
    contents = re.sub('ö', r"\"o", contents)
    contents = re.sub('Ö', r"\"O", contents)
    contents = re.sub('ñ', r"\~n", contents)
    contents = re.sub('Ñ', r"\~N", contents)
    contents = re.sub('¡', r"!`", contents)
    contents = re.sub('¿', r"?`", contents)
    contents = re.sub('<strong>([^<]*)</strong>', r"{\\bf \1}", contents)
    contents = re.sub('<em>([^<]*)</em>', r"{\\em \1}", contents)
    contents = re.sub('<h2>([^<]*)</h2>', r"\\subsection{\1}", contents)
    contents = re.sub('<ul>', r"\\begin{itemize}", contents)
    contents = re.sub('</ul>', r"\\end{itemize}", contents)
    contents = re.sub('<ol>', r"\\begin{enumerate}", contents)
    contents = re.sub('</ol>', r"\\end{enumerate}", contents)
    contents = re.sub('<li>', r"\\item ", contents)
    contents = re.sub('<a href="/([^"]*)">([^<]*)</a>', r"\\hyperref[\1]{\2}", contents)
    contents = re.sub('[%][%][^{]*[{]([^%]*)[%][%][}]', r'\\begin{center}\1\\end{center}', contents)
    return contents

def latex(bare_contents, slug=None):
    return r'''
              \documentclass{article}
              <<INCLUDES>>
              \begin{document}
              <<CONTENTS>>
              \end{document}
           '''.replace('<<CONTENTS>>', wrap_latex(bare_contents, slug)).replace('<<INCLUDES>>', latex_includes())

def upload_attachments(to, gmail_user, gmail_pwd, attachment_names):
    for attachment in attachment_names:
        file_to_upload = 'media/%s.png' % (attachment,)
        if not os.path.exists(file_to_upload):
            print '!!! error: attachment %s was not generated correctly' % (attachment,)
            sys.exit(1)

    to = 'media+' + to
    for attachment in attachment_names:
        print 'uploading attachment for %s' % (attachment,)
        file_to_upload = 'media/%s.png' % (attachment,)

        content = MIMEMultipart()
        content['From'] = gmail_user
        content['To'] = to
        content['Subject'] = 'attachment %s\n' % (attachment,)
        img = MIMEImage(file(file_to_upload).read())
        img.add_header('Content-Type', 'image/png', name=attachment + '.png')
        img.add_header('Content-Disposition', 'attachment', filename=attachment + '.png')
        content.attach(img)
        msg = content.as_string()

        smtpserver = smtplib.SMTP("smtp.gmail.com", 587)
        smtpserver.ehlo()
        smtpserver.starttls()
        smtpserver.ehlo
        smtpserver.login(gmail_user, gmail_pwd)
        smtpserver.sendmail(gmail_user, to, msg)
        smtpserver.close()

def post_contents(slug, bare_contents):
    attachment_sizes = make_attachments(slug, bare_contents)
    contents = wordpress(slug, bare_contents, attachment_sizes)

    if '[tags inconcluso]' in contents:
        print
        print '! Post contaings tag "inconcluso".'
        print '! Add tags and resubmit.'
        print
        sys.exit(1)

    to, gmail_user, blog_name = read_conf_file()
    gmail_pwd = getpass.getpass('%s password: ' % (gmail_user,))

    upload_attachments(to, gmail_user, gmail_pwd, sorted(attachment_sizes.keys()))

    print 'uploading post'
    smtpserver = smtplib.SMTP("smtp.gmail.com", 587)
    smtpserver.ehlo()
    smtpserver.starttls()
    smtpserver.ehlo
    smtpserver.login(gmail_user, gmail_pwd)
    header = 'To:' + to + '\n' + 'From: ' + gmail_user + '\n' + 'Subject: post %s\n' % (slug,)
    msg = header + '\n' + contents
    smtpserver.sendmail(gmail_user, to, msg)
    smtpserver.close()

def view_contents(slug, contents):
    f = file('%s.tex' % (slug,), 'w')
    f.write(contents)
    f.close()
    #os.system('pdflatex %s.tex && evince %s.pdf' % (slug, slug))
    os.system('_pdflatex_evince %s.tex' % (slug,))

def filename_variations(filename):
    yield filename
    yield filename + '.pruf'
    yield filename + 'pruf'

def normalize_filename(filename):
    if not filename.endswith('.pruf'):
        if not filename.endswith('.'):
            filename += '.'
        filename += 'pruf'
    return filename

def usage():
    name = sys.argv[0]
    print 'Usage:'
    print '    %s (n)ew  file[.pruf]' % (name,)
    print '    %s (v)iew file[.pruf]' % (name,)
    print '    %s (p)ost file[.pruf]' % (name,)
    print '    %s (b)uild' % (name,)
    print '    %s (c)lean' % (name,)
    sys.exit(1)

def read_contents(filename):
    slug = slug_for(filename)
    for fn in filename_variations(filename):
        if os.path.exists(fn):
            filename = fn
            break

    if not os.path.exists(filename):
        print 'Error: %s -- does not exist' % (filename,)
        sys.exit(1)

    f = file(filename, 'r')
    bare_contents = f.read()
    f.close()
    return slug, bare_contents

def slug_for(fn):
    return fn.split('.')[0]

def create_new(filename):
    assert not os.path.exists(filename)
    f = file(filename, 'w')
    f.write('[title %s]\n' % (slug_for(filename),))
    if os.path.exists('MATERIA'):
        g = file('MATERIA', 'r')
        materia = g.readline().strip(' \t\r\n')
        g.close()
    else:
        materia = '...'
    f.write('[category %s]\n' % (materia,))
    f.write('[tags inconcluso]\n\n')
    f.close()

def latex_includes():
    return '''
               \usepackage{amsmath,amssymb}
               \usepackage[all]{xy}
               \usepackage{hyperref}
    '''

def build_latex(basedir='done'):
    full = [] 
    for fn in os.listdir('%s/' % (basedir,)):
        if fn.endswith('.pruf'):
            f = file('%s/%s' % (basedir, fn))
            full.append(wrap_latex(f.read(), slug=slug_for(fn)))
            f.close()
    return r'''
              \documentclass{article}
              <<INCLUDES>>
              \title{!`Pruf!\\{\Large Cocientar es olvidar diferencias}}
              \author{}
              \date{}
              \begin{document}
              \sf
              \maketitle
              \tableofcontents
              <<CONTENTS>>
              \end{document}
           '''.replace('<<CONTENTS>>', '\n'.join(full)).replace('<<INCLUDES>>', latex_includes())

def clean(basename):
    exts = ['pdf', 'tex', 'aux', 'log', 'toc', 'out']
    print 'Cleaning %s.{%s}' % (basename, ','.join(exts))
    os.system('rm -f %s' % (' '.join(['%s.%s' % (basename, ext) for ext in exts]),))

def done(fn):
    clean(slug_for(fn))
    hg_status = os.popen('hg status %s' % (fn,)).read()
    if '?' in hg_status:
        os.system('mv %s done/' % (fn,))
        os.system('hg add done/%s' % (fn,))
    else:
        os.system('hg mv %s done/' % (fn,))

def main(args):

    if len(args) < 2:
        usage()

    if args[1] in ['v', 'view']:
        if len(args) != 3: usage()
        slug, bare_contents = read_contents(args[2])
        view_contents(slug, latex(bare_contents, slug))

    elif args[1] in ['p', 'post']:
        if len(args) != 3: usage()
        slug, bare_contents = read_contents(args[2])
        post_contents(slug, bare_contents)

        fn = normalize_filename(args[2])
        done(fn)
        print 'DONE'

    elif args[1] in ['w', 'wordpress']:
        if len(args) != 3: usage()
        slug, bare_contents = read_contents(args[2])
        contents = wordpress(slug, bare_contents, {})
        print contents

    elif args[1] in ['c', 'clean']:
        for fn in os.listdir('.'):
          if fn.endswith('.pruf'):
              clean(slug_for(fn))
        clean('Pruf')

    elif args[1] in ['n', 'new']:
        if len(args) != 3: usage()
        filename = normalize_filename(args[2])
        if os.path.exists(filename):
            print 'Error: %s -- already exists' % (filename,)
            sys.exit(1)
        else:
            create_new(filename)
            print 'Created', filename
            os.system('vim %s' % (filename,))

    elif args[1] in ['b', 'build']:
        view_contents('Pruf', build_latex())

    else:
        usage()

main(sys.argv)

