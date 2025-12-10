use super::SmtParser;

#[derive(Debug)]
pub struct ExtractedSampleId {
    pub smtfunname: String,
    pub pkgname: String,
    pub oraclename: String,
    pub samplename: String,
}

impl std::fmt::Display for ExtractedSampleId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let ExtractedSampleId {
            smtfunname: _,
            pkgname,
            oraclename,
            samplename,
        } = self;
        write!(
            f,
            "(sample-id \"{pkgname}\" \"{oraclename}\" \"{samplename}\")"
        )
    }
}

impl ExtractedSampleId {
    fn new(pkgname: &str, oraclename: &str, samplename: &str) -> Self {
        Self {
            smtfunname: String::new(),
            pkgname: pkgname.to_string(),
            oraclename: oraclename.to_string(),
            samplename: samplename.to_string(),
        }
    }

    fn set_smtfun(&mut self, smtfunname: &str) {
        self.smtfunname = smtfunname.to_string()
    }
}

struct SampleIdExtractor {
    sample_ids: Vec<ExtractedSampleId>,
}

impl SampleIdExtractor {
    fn new() -> Self {
        Self {
            sample_ids: Vec::new(),
        }
    }
}

impl SmtParser<Vec<ExtractedSampleId>> for SampleIdExtractor {
    fn handle_atom(&mut self, _content: &str) -> Vec<ExtractedSampleId> {
        Vec::new()
    }

    fn handle_list(&mut self, content: Vec<Vec<ExtractedSampleId>>) -> Vec<ExtractedSampleId> {
        content.into_iter().flatten().collect()
    }
    fn handle_sexp(&mut self, mut parsed: Vec<ExtractedSampleId>) {
        self.sample_ids.append(&mut parsed);
    }

    fn handle_sampleid(
        &mut self,
        pkgname: &str,
        oraclename: &str,
        samplename: &str,
    ) -> Vec<ExtractedSampleId> {
        vec![ExtractedSampleId::new(pkgname, oraclename, samplename)]
    }

    fn handle_definefun(
        &mut self,
        funname: &str,
        _args: Vec<Vec<ExtractedSampleId>>,
        _ty: &str,
        body: Vec<ExtractedSampleId>,
    ) -> Vec<ExtractedSampleId> {
        body.into_iter()
            .map(|mut sampleid| {
                sampleid.set_smtfun(funname);
                sampleid
            })
            .collect()
    }
}

pub fn extract(content: &str) -> Vec<ExtractedSampleId> {
    let mut extractor = SampleIdExtractor::new();
    extractor.parse_sexps(content);

    extractor.sample_ids
}
