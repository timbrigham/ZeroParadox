"""Download DejaVu fonts required by the Zero Paradox PDF builders."""

import urllib.request, os, zipfile, io

URL = 'https://github.com/dejavu-fonts/dejavu-fonts/releases/download/version_2_37/dejavu-fonts-ttf-2.37.zip'
NEEDED = [
    'DejaVuSans.ttf', 'DejaVuSans-Bold.ttf',
    'DejaVuSans-Oblique.ttf', 'DejaVuSans-BoldOblique.ttf',
    'DejaVuSerif.ttf', 'DejaVuSerif-Bold.ttf',
    'DejaVuSerif-Italic.ttf', 'DejaVuSerif-BoldItalic.ttf',
]

def main():
    font_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'fonts')
    os.makedirs(font_dir, exist_ok=True)

    already = [f for f in NEEDED if os.path.exists(os.path.join(font_dir, f))]
    if len(already) == len(NEEDED):
        print('All fonts already present.')
        return

    print('Downloading DejaVu fonts...')
    data = urllib.request.urlopen(URL, timeout=60).read()
    print(f'Downloaded {len(data) // 1024}KB')

    z = zipfile.ZipFile(io.BytesIO(data))
    for member in z.namelist():
        fname = os.path.basename(member)
        if fname in NEEDED:
            dest = os.path.join(font_dir, fname)
            with open(dest, 'wb') as f:
                f.write(z.read(member))
            print(f'  {fname}')

    print('Done.')

if __name__ == '__main__':
    main()
