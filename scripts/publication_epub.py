"""Normalize TeX4ht EPUB navigation and metadata, preserving native MathML."""
from pathlib import PurePosixPath
import posixpath
from urllib.parse import unquote, urlsplit
import uuid
import zipfile

from lxml import etree

XHTML = "http://www.w3.org/1999/xhtml"
OPF = "http://www.idpf.org/2007/opf"
DC = "http://purl.org/dc/elements/1.1/"
EPUB = "http://www.idpf.org/2007/ops"
MATH = "http://www.w3.org/1998/Math/MathML"
NCX = "http://www.daisy.org/z3986/2005/ncx/"
NS = {"h": XHTML, "opf": OPF, "dc": DC, "m": MATH}


def text(element):
    return " ".join("".join(element.itertext()).split())


def serialize(element):
    return etree.tostring(element, encoding="utf-8", xml_declaration=True)


def normalize_epub(source, target, metadata, version, asset_root=None):
    with zipfile.ZipFile(source) as archive:
        files = {name: archive.read(name) for name in archive.namelist()}
    container = etree.fromstring(files["META-INF/container.xml"])
    opf_path = container.xpath("//*[local-name()='rootfile']/@full-path")[0]
    base = posixpath.dirname(opf_path)
    package = etree.fromstring(files[opf_path])
    manifest = package.find("opf:manifest", NS)
    spine = package.find("opf:spine", NS)
    items = {item.get("id"): item for item in manifest}
    docs = {}
    for item in manifest:
        if item.get("media-type") == "application/xhtml+xml":
            name = posixpath.normpath(posixpath.join(base, item.get("href")))
            document = etree.fromstring(files[name])
            # A line break separates the label visually, but contributes no
            # text when navigation labels are extracted or readers omit it.
            for heading in document.xpath("//h:h1 | //h:h2 | //h:h3", namespaces=NS):
                if not {"chapterHead", "appendixHead"}.intersection(heading.get("class", "").split()):
                    continue
                for mark in heading.findall("h:span", NS):
                    if "titlemark" in mark.get("class", "").split():
                        mark.tail = " " + (mark.tail or "").lstrip()
            docs[item.get("id")] = (name, document)
    nav_item = next(item for item in manifest if "nav" in item.get("properties", "").split())
    nav_id = nav_item.get("id")
    nav_path, nav_doc = docs[nav_id]
    nav_base = posixpath.dirname(nav_path)
    entries = []
    math_count = 0
    for ref in spine:
        doc_id = ref.get("idref")
        if doc_id not in docs or doc_id == nav_id:
            continue
        ref.attrib.pop("linear", None)
        path, document = docs[doc_id]
        title = document.find("h:head/h:title", NS)
        title_text = text(title) if title is not None else "Book"
        headings = document.xpath("//h:h1 | //h:h2 | //h:h3", namespaces=NS)
        # The first heading is the chapter/front-matter title. Keep the next
        # heading level as children; theorem headings remain in the body.
        top = headings[0] if headings else None
        title_text = text(top) if top is not None else title_text
        if top is None:
            title_text = "Title and edition information"
        href = posixpath.relpath(path, nav_base)
        children = []
        if top is not None:
            top.set("id", top.get("id", "publication-title"))
            href += "#" + top.get("id")
            top_level = int(etree.QName(top).localname[1])
            for number, heading in enumerate(headings[1:], 1):
                if int(etree.QName(heading).localname[1]) == top_level + 1:
                    heading.set("id", heading.get("id", f"publication-section-{number}"))
                    children.append((text(heading), posixpath.relpath(path, nav_base) + "#" + heading.get("id")))
        entries.append((title_text, href, children))
        # TeX4ht uses ordinal indexing markers, not stable EPUB page numbers.
        # Name these destinations as passages so they are meaningful in a
        # reflowable edition at any reader font size.
        if title_text in ("Index", "Index of Notation"):
            for paragraph in document.xpath("//h:p", namespaces=NS):
                for number, link in enumerate(paragraph.xpath(".//h:a[@href]", namespaces=NS), 1):
                    if text(link).isdigit():
                        link.text = f"passage {number}"
        math_count += len(document.findall(".//m:math", NS))
    # Replace the malformed old AMS starred-chapter TOC with one generated
    # directly from the ordered spine and the actual content headings.
    body = nav_doc.find("h:body", NS)
    body.clear()
    heading = etree.SubElement(body, f"{{{XHTML}}}h1")
    heading.text = "Contents"
    nav = etree.SubElement(body, f"{{{XHTML}}}nav", {f"{{{EPUB}}}type": "toc", "id": "toc"})
    ordered = etree.SubElement(nav, f"{{{XHTML}}}ol")
    for label, href, children in entries:
        li = etree.SubElement(ordered, f"{{{XHTML}}}li")
        etree.SubElement(li, f"{{{XHTML}}}a", href=href).text = label
        if children:
            sub = etree.SubElement(li, f"{{{XHTML}}}ol")
            for child_label, child_href in children:
                subli = etree.SubElement(sub, f"{{{XHTML}}}li")
                etree.SubElement(subli, f"{{{XHTML}}}a", href=child_href).text = child_label
    landmarks = etree.SubElement(body, f"{{{XHTML}}}nav", {f"{{{EPUB}}}type": "landmarks", "hidden": "hidden"})
    landmark_list = etree.SubElement(landmarks, f"{{{XHTML}}}ol")
    li = etree.SubElement(landmark_list, f"{{{XHTML}}}li")
    first_chapter = next(entry for entry in entries if "Finite Relational Structures and Symmetry" in entry[0])
    etree.SubElement(li, f"{{{XHTML}}}a", {"href": first_chapter[1], f"{{{EPUB}}}type": "bodymatter"}).text = "Begin reading"
    # Correct per-document manifest properties, including the TOC's removal
    # of incidental math. No JavaScript or external renderer is required.
    for doc_id, (name, document) in docs.items():
        item = items[doc_id]
        properties = set(item.get("properties", "").split()) - {"mathml"}
        if document.find(".//m:math", NS) is not None:
            properties.add("mathml")
        if properties:
            item.set("properties", " ".join(sorted(properties)))
        else:
            item.attrib.pop("properties", None)
        # A display equation is commonly emitted inside an XHTML table.
        # Bound that table's width and allow local horizontal scrolling;
        # otherwise long formulas force the entire ebook page to overflow
        # on a phone or at a large reader font setting.
        for table in document.findall(".//h:table", NS):
            parent = table.getparent()
            wrapper = etree.Element(f"{{{XHTML}}}div", {"class": "publication-table-scroll"})
            wrapper.tail = table.tail
            table.tail = None
            parent.replace(table, wrapper)
            wrapper.append(table)
        # Aligned displays can also be emitted directly as block MathML.
        # Use a span so the wrapper remains valid even inside a paragraph.
        for formula in document.findall(".//m:math[@display='block']", NS):
            if any("publication-table-scroll" in ancestor.get("class", "").split()
                   for ancestor in formula.iterancestors()):
                continue
            parent = formula.getparent()
            wrapper = etree.Element(f"{{{XHTML}}}span", {"class": "publication-table-scroll"})
            wrapper.tail = formula.tail
            formula.tail = None
            parent.replace(formula, wrapper)
            wrapper.append(formula)
        for image in document.findall(".//h:img", NS):
            src = image.get("src", "")
            if urlsplit(src).scheme:
                raise ValueError("EPUB images must be packaged locally: " + src)
            resource = posixpath.normpath(posixpath.join(posixpath.dirname(name), unquote(src)))
            if resource not in files:
                relative = posixpath.relpath(resource, base)
                if not relative.startswith("results/figures/") or asset_root is None:
                    raise ValueError("Missing EPUB asset: " + resource)
                original = asset_root / relative
                if not original.is_file():
                    raise ValueError("Missing source image: " + str(original))
                files[resource] = original.read_bytes()
                media = {".png": "image/png", ".jpg": "image/jpeg", ".jpeg": "image/jpeg"}[original.suffix]
                etree.SubElement(manifest, f"{{{OPF}}}item", href=relative,
                                 id="asset-" + str(len(manifest)), **{"media-type": media})
            if image.get("alt", "") in ("", "PIC"):
                label = PurePosixPath(src).stem.replace("_", " ").replace("-epub", "")
                image.set("alt", "Figure: " + label)
        files[name] = serialize(document)
    meta = package.find("opf:metadata", NS)
    cover_name = metadata.get("cover_image")
    if cover_name:
        relative = PurePosixPath(cover_name)
        if relative.is_absolute() or ".." in relative.parts or asset_root is None:
            raise ValueError("Cover image must be a relative path in the private book checkout")
        cover = asset_root / cover_name
        media = {".png": "image/png", ".jpg": "image/jpeg", ".jpeg": "image/jpeg"}.get(cover.suffix.lower())
        if media is None:
            raise ValueError("Use a PNG or JPEG ebook cover")
        # KDP requests an OPF cover-image entry, without an additional HTML
        # cover page that could produce a duplicate during Kindle conversion.
        for item in manifest:
            properties = item.get("properties", "").split()
            if "cover-image" in properties:
                properties.remove("cover-image")
                if properties:
                    item.set("properties", " ".join(properties))
                else:
                    item.attrib.pop("properties", None)
        cover_href = "images/kindle-cover" + cover.suffix.lower()
        files[posixpath.join(base, cover_href)] = cover.read_bytes()
        etree.SubElement(manifest, f"{{{OPF}}}item", id="publication-cover-image", href=cover_href,
                         properties="cover-image", **{"media-type": media})
        for old in meta.xpath("opf:meta[@name='cover']", namespaces=NS):
            meta.remove(old)
        etree.SubElement(meta, f"{{{OPF}}}meta", name="cover", content="publication-cover-image")
    full_title = metadata["title"] + ": " + metadata["subtitle"]
    for key, value in (("title", full_title), ("creator", metadata["author"]),
                       ("language", metadata["language"])):
        element = meta.find("dc:" + key, NS)
        if element is None:
            element = etree.SubElement(meta, f"{{{DC}}}{key}")
        element.text = value
    identifier = "urn:uuid:" + str(uuid.uuid5(uuid.NAMESPACE_URL, full_title + ":" + version))
    meta.find("dc:identifier", NS).text = identifier
    etree.SubElement(meta, f"{{{DC}}}description").text = f"{metadata['edition']}; version {version}; {metadata['status']}."
    files[opf_path] = serialize(package)
    for item in manifest:
        if item.get("media-type") == "text/css":
            path = posixpath.join(base, item.get("href"))
            files[path] += b"\n.publication-table-scroll { display:block; max-width:100%; overflow-x:auto; margin:1em 0; }\n"
    # Keep the NCX in agreement for readers that use the compatibility TOC.
    ncx_item = next((item for item in manifest if item.get("media-type") == "application/x-dtbncx+xml"), None)
    if ncx_item is not None:
        ncx_path = posixpath.join(base, ncx_item.get("href"))
        ncx = etree.Element(f"{{{NCX}}}ncx", nsmap={None: NCX}, version="2005-1")
        head = etree.SubElement(ncx, f"{{{NCX}}}head")
        etree.SubElement(head, f"{{{NCX}}}meta", name="dtb:uid", content=identifier)
        dt = etree.SubElement(ncx, f"{{{NCX}}}docTitle")
        etree.SubElement(dt, f"{{{NCX}}}text").text = full_title
        nav_map = etree.SubElement(ncx, f"{{{NCX}}}navMap")
        order = 0
        for label, href, children in entries:
            order += 1
            point = etree.SubElement(nav_map, f"{{{NCX}}}navPoint", id=f"nav-{order}", playOrder=str(order))
            nl = etree.SubElement(point, f"{{{NCX}}}navLabel")
            etree.SubElement(nl, f"{{{NCX}}}text").text = label
            etree.SubElement(point, f"{{{NCX}}}content", src=href)
        files[ncx_path] = serialize(ncx)
    with zipfile.ZipFile(target, "w") as archive:
        archive.writestr("mimetype", b"application/epub+zip", compress_type=zipfile.ZIP_STORED)
        for name, data in files.items():
            if name != "mimetype" and not name.endswith("/"):
                archive.writestr(name, data, compress_type=zipfile.ZIP_DEFLATED)
    return {"native_mathml_expressions": math_count, "navigation_entries": len(entries),
            "xhtml_documents": len(docs), "identifier": identifier,
            "embedded_cover": bool(cover_name)}
