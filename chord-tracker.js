/* Song Rider Pro - root-first harmonic chord tracker engine
   Browser mic audio -> stable simple chord labels for songwriting use.
   Exposes window.SongRiderChordTracker.create()

   v ROOT_FIRST_1
   Goal: prefer correct root-position G/C/D/Am/F style chords over relative guesses
   (G->Em, C->Am, D->F) by estimating note fundamentals with harmonic summing
   instead of voting raw bright FFT partials as chord tones.
*/
(function(){
  'use strict';

  const ROOTS = ["C","C#","D","D#","E","F","F#","G","G#","A","A#","B"];
  const ALLOWED = new Set(["C","D","E","F","G","A","B","Cm","C#m","Dm","D#m","Em","Fm","F#m","Gm","G#m","Am","A#m","Bm"]);
  const clamp01 = (n) => Math.max(0, Math.min(1, Number(n) || 0));
  const freqToMidi = (f) => 69 + 12 * Math.log2(f / 440);
  const normPc = (pc) => ((Math.round(pc) % 12) + 12) % 12;
  const pcName = (pc) => ROOTS[normPc(pc)];

  function cleanLabel(value){
    let out = String(value || '').trim();
    if(!out) return '';
    out = out.replace(/♯/g,'#').replace(/♭/g,'b').replace(/\s+/g,'');
    const m = out.match(/^([A-Ga-g])([#b]?)(.*)$/);
    if(!m) return out;
    const root = m[1].toUpperCase() + (m[2] || '');
    let rest = String(m[3] || '');
    rest = rest.replace(/^minor$/i,'m').replace(/^min$/i,'m').replace(/^-/,'m');
    if(rest === 'maj' || rest === 'M') rest = '';
    return root + rest;
  }

  function create(){
    const state = {
      frames: [],
      candidateKey: '',
      candidateSince: 0,
      candidateCount: 0,
      locked: null,
      lockedAt: 0,
      lastResult: null,
      noiseFloor: 0.0030,
      lastDebug: null
    };

    const cfg = {
      minFreq: 52,
      maxFreq: 1800,
      fundamentalMin: 48,
      fundamentalMax: 1050,
      keepMs: 1350,
      minDb: -98,
      maxPeaks: 96,
      silenceRmsFloor: 0.0038,
      chordStableMs: 460,
      noteStableMs: 280,
      chordMinConfidence: 0.48,
      noteMinConfidence: 0.50
    };

    function reset(){
      state.frames = [];
      state.candidateKey = '';
      state.candidateSince = 0;
      state.candidateCount = 0;
      state.locked = null;
      state.lockedAt = 0;
      state.lastResult = null;
      state.lastDebug = null;
    }

    function getFreqData(analyser){
      if(!analyser) return null;
      if(!state.freqBuf || state.freqBuf.length !== analyser.frequencyBinCount){
        state.freqBuf = new Float32Array(analyser.frequencyBinCount);
      }
      analyser.getFloatFrequencyData(state.freqBuf);
      return state.freqBuf;
    }

    function getTimeData(analyser){
      if(!analyser) return null;
      if(!state.timeBuf || state.timeBuf.length !== analyser.fftSize){
        state.timeBuf = new Float32Array(analyser.fftSize);
      }
      analyser.getFloatTimeDomainData(state.timeBuf);
      return state.timeBuf;
    }

    function rms(buf){
      if(!buf || !buf.length) return 0;
      let s = 0;
      for(let i=0;i<buf.length;i++) s += buf[i] * buf[i];
      return Math.sqrt(s / buf.length);
    }

    function detectSinglePitch(buf, sampleRate, level){
      if(!buf || !buf.length || !sampleRate || level < cfg.silenceRmsFloor) return null;
      const n = Math.min(buf.length, 4096);
      const minLag = Math.max(2, Math.floor(sampleRate / 1100));
      const maxLag = Math.min(n - 2, Math.ceil(sampleRate / 60));
      let bestLag = -1, bestCorr = 0;
      for(let lag=minLag; lag<=maxLag; lag++){
        let sum = 0, aa = 0, bb = 0;
        const usable = n - lag;
        for(let i=0;i<usable;i++){
          const a = buf[i], b = buf[i+lag];
          sum += a*b; aa += a*a; bb += b*b;
        }
        const corr = sum / (Math.sqrt(aa*bb) || 1);
        if(corr > bestCorr){ bestCorr = corr; bestLag = lag; }
      }
      if(bestLag <= 0 || bestCorr < 0.44) return null;
      const freq = sampleRate / bestLag;
      const midi = freqToMidi(freq);
      const pc = normPc(midi);
      return { pc, note: ROOTS[pc], confidence: clamp01(bestCorr * Math.min(1, level / 0.032)) };
    }

    function pickSpectralPeaks(data, sampleRate, fftSize){
      const binHz = sampleRate / fftSize;
      const peaks = [];
      let maxDb = -Infinity;
      for(let i=2;i<data.length-2;i++){
        const db = data[i];
        if(Number.isFinite(db) && db > maxDb) maxDb = db;
      }
      if(!Number.isFinite(maxDb) || maxDb < -90) return [];

      // Relative floor follows the actual input so a quiet piano is still read,
      // but room noise does not become fake chords.
      const floor = Math.max(cfg.minDb, maxDb - 56);
      for(let i=2;i<data.length-2;i++){
        const db = data[i];
        if(!Number.isFinite(db) || db < floor) continue;
        const freq = i * binHz;
        if(freq < cfg.minFreq || freq > cfg.maxFreq) continue;
        if(db < data[i-1] || db < data[i+1]) continue;
        if(db < data[i-2] || db < data[i+2]) continue;
        const amp = Math.pow(10, db / 20);
        peaks.push({ freq, amp, db });
      }
      peaks.sort((a,b) => b.amp - a.amp);
      return peaks.slice(0, cfg.maxPeaks);
    }

    function addVote(arr, pc, w){
      pc = normPc(pc);
      arr[pc] += Math.max(0, Number(w) || 0);
    }

    function buildChromaFromPeaks(peaks){
      if(!peaks || !peaks.length) return null;
      const direct = Array(12).fill(0);
      const fundamental = Array(12).fill(0);
      const bass = Array(12).fill(0);
      const rootBand = Array(12).fill(0);
      const topAmp = peaks[0].amp || 1;

      // Direct note energy: useful for the third/fifth.
      for(const pk of peaks){
        const midi = freqToMidi(pk.freq);
        const nearest = Math.round(midi);
        const cents = Math.abs((midi - nearest) * 100);
        if(cents > 38) continue;
        const pc = normPc(nearest);
        const ampNorm = Math.max(0, pk.amp / topAmp);
        let w = Math.pow(ampNorm, 0.70) * (1 - cents / 54);
        if(pk.freq > 650) w *= 0.50;
        if(pk.freq > 1100) w *= 0.30;
        if(pk.freq >= 65 && pk.freq <= 620) w *= 1.16;
        addVote(direct, pc, w);
      }

      // Harmonic summing: every bright peak is treated as possible 2nd/3rd/4th/etc.
      // harmonic of a lower note. This is the main fix for phone mic piano overtones.
      for(const pk of peaks){
        const ampNorm = Math.max(0, pk.amp / topAmp);
        if(ampNorm < 0.012) continue;
        for(let h=1; h<=7; h++){
          const f0 = pk.freq / h;
          if(f0 < cfg.fundamentalMin || f0 > cfg.fundamentalMax) continue;
          const midi = freqToMidi(f0);
          const nearest = Math.round(midi);
          const cents = Math.abs((midi - nearest) * 100);
          if(cents > 36) continue;
          const pc = normPc(nearest);
          let w = Math.pow(ampNorm, 0.72) * (1 - cents / 48) / Math.pow(h, 1.20);
          if(h === 1) w *= 0.72; // direct already counts h=1; prevent double-bright partial bias
          if(f0 >= 60 && f0 <= 360) w *= 1.22;
          if(f0 > 650) w *= 0.58;
          addVote(fundamental, pc, w);
          if(f0 >= 52 && f0 <= 260) addVote(bass, pc, w * (f0 < 150 ? 1.35 : 1.0));
          if(f0 >= 65 && f0 <= 210) addVote(rootBand, pc, w * 1.35);
        }
      }

      function normalize(arr, softFloor=0.06){
        const max = Math.max(...arr);
        if(max <= 0) return false;
        for(let i=0;i<12;i++){
          arr[i] = arr[i] / max;
          if(arr[i] < softFloor) arr[i] = 0;
        }
        return true;
      }
      if(!normalize(direct, 0.07) && !normalize(fundamental, 0.07)) return null;
      normalize(fundamental, 0.07);
      normalize(bass, 0.05);
      normalize(rootBand, 0.05);

      const chroma = Array(12).fill(0);
      for(let i=0;i<12;i++){
        // Fundamental carries the chord ID, direct carries color/third support.
        chroma[i] = Math.max(fundamental[i] * 0.72 + direct[i] * 0.44, direct[i] * 0.72);
      }
      normalize(chroma, 0.08);
      return { chroma, bass, rootBand, direct, fundamental };
    }

    function pushFrame(frame, nowMs){
      state.frames.push({ ...frame, t: nowMs });
      const cutoff = nowMs - cfg.keepMs;
      while(state.frames.length && state.frames[0].t < cutoff) state.frames.shift();
    }

    function aggregate(){
      const frames = state.frames;
      if(!frames.length) return null;
      const chroma = Array(12).fill(0);
      const bass = Array(12).fill(0);
      const rootBand = Array(12).fill(0);
      const direct = Array(12).fill(0);
      const fundamental = Array(12).fill(0);
      const pitchVotes = Array(12).fill(0);
      let cFrames = 0, rmsSum = 0;
      for(const fr of frames){
        rmsSum += Number(fr.level) || 0;
        if(Array.isArray(fr.chroma)){
          cFrames++;
          for(let i=0;i<12;i++) chroma[i] += Number(fr.chroma[i]) || 0;
        }
        for(const key of ['bass','rootBand','direct','fundamental']){
          if(Array.isArray(fr[key])){
            const arr = key === 'bass' ? bass : key === 'rootBand' ? rootBand : key === 'direct' ? direct : fundamental;
            for(let i=0;i<12;i++) arr[i] += Number(fr[key][i]) || 0;
          }
        }
        if(Number.isFinite(fr.pitchPc)){
          pitchVotes[fr.pitchPc] += Math.max(0.04, Number(fr.pitchConfidence) || 0.04);
        }
      }
      if(!cFrames) return null;
      for(const arr of [chroma,bass,rootBand,direct,fundamental]){
        for(let i=0;i<12;i++) arr[i] /= cFrames;
      }
      const pvMax = Math.max(...pitchVotes);
      if(pvMax > 0){
        for(let i=0;i<12;i++) chroma[i] += 0.045 * (pitchVotes[i] / pvMax);
      }
      const max = Math.max(...chroma);
      if(max <= 0) return null;
      for(let i=0;i<12;i++) chroma[i] /= max;
      const strongNotes = chroma.map((v,i)=>({pc:i,v})).filter(x => x.v >= 0.25).sort((a,b)=>b.v-a.v);
      const bassMax = Math.max(...bass);
      const likelyBassPc = bassMax > 0 ? bass.indexOf(bassMax) : null;
      const rootBandMax = Math.max(...rootBand);
      const likelyRootPc = rootBandMax > 0 ? rootBand.indexOf(rootBandMax) : likelyBassPc;
      const pitchPc = pvMax > 0 ? pitchVotes.indexOf(pvMax) : null;
      return { chroma, bass, rootBand, direct, fundamental, frameCount: frames.length, strongNotes, pitchPc, likelyBassPc, likelyRootPc, pitchConfidence: pvMax / Math.max(1, frames.length), avgLevel: rmsSum / frames.length };
    }

    function templateCandidates(agg){
      const chroma = agg.chroma;
      const bass = agg.bass || Array(12).fill(0);
      const rootBand = agg.rootBand || bass;
      const direct = agg.direct || chroma;
      const fund = agg.fundamental || chroma;
      const v = (pc) => Number(chroma[normPc(pc)]) || 0;
      const b = (pc) => Number(bass[normPc(pc)]) || 0;
      const rb = (pc) => Number(rootBand[normPc(pc)]) || 0;
      const d = (pc) => Number(direct[normPc(pc)]) || 0;
      const f = (pc) => Number(fund[normPc(pc)]) || 0;
      const templates = [
        { suffix:'',  pcs:[0,4,7], type:'maj' },
        { suffix:'m', pcs:[0,3,7], type:'min' }
      ];
      const out = [];
      for(let root=0; root<12; root++){
        for(const tpl of templates){
          const label = ROOTS[root] + tpl.suffix;
          if(!ALLOWED.has(label)) continue;
          const pcs = tpl.pcs.map(x => normPc(root + x));
          const rootE = v(root), fifth = v(root+7);
          const maj3 = v(root+4), min3 = v(root+3);
          const third = tpl.type === 'maj' ? maj3 : min3;
          const wrongThird = tpl.type === 'maj' ? min3 : maj3;
          const need = pcs.reduce((s,pc)=>s + v(pc),0) / pcs.length;
          const directNeed = pcs.reduce((s,pc)=>s + d(pc),0) / pcs.length;
          const fundNeed = pcs.reduce((s,pc)=>s + f(pc),0) / pcs.length;
          const outside = chroma.reduce((s,x,pc)=>s + (pcs.includes(pc) ? 0 : Math.max(0,x)),0) / 12;
          const weakest = Math.min(...pcs.map(pc => v(pc)));
          const bassRoot = b(root);
          const rootBandRoot = rb(root);
          let score = 0;
          score += need * 0.58;
          score += fundNeed * 0.25;
          score += directNeed * 0.12;
          score += rootE * 0.20;
          score += fifth * 0.11;
          score += bassRoot * 0.34;
          score += rootBandRoot * 0.24;
          score += third * 0.22;
          score -= wrongThird * (tpl.type === 'maj' ? 0.21 : 0.26);
          score -= outside * 0.33;
          if(agg.pitchPc === root) score += 0.030;
          if(agg.likelyBassPc === root) score += 0.11;
          if(agg.likelyRootPc === root) score += 0.10;
          out.push({ root, suffix:tpl.suffix, type:tpl.type, label, pcs, score, need, directNeed, fundNeed, weakest, rootE, fifth, maj3, min3, third, wrongThird, bassRoot, rootBandRoot });
        }
      }
      out.sort((a,b)=>b.score-a.score);
      return out;
    }

    function chooseRootFirstCandidate(candidates, agg){
      if(!candidates.length) return null;
      let best = candidates[0];
      const rootPc = Number.isFinite(agg.likelyRootPc) ? agg.likelyRootPc : agg.likelyBassPc;
      if(Number.isFinite(rootPc)){
        const rootCandidates = candidates.filter(c => c.root === rootPc && c.need >= 0.27 && c.third >= 0.16 && c.fifth >= 0.13);
        if(rootCandidates.length){
          rootCandidates.sort((a,b)=>b.score-a.score);
          const rb = rootCandidates[0];
          // Prefer the low/root-supported chord unless the global best is far better.
          if(rb.score >= best.score - 0.20) best = rb;
        }
      }
      return best;
    }

    function inferChord(agg){
      if(!agg || !Array.isArray(agg.chroma)) return null;
      if(agg.strongNotes.length < 3) return null;
      const candidates = templateCandidates(agg);
      let best = chooseRootFirstCandidate(candidates, agg);
      if(!best) return null;
      let second = candidates.find(c => c !== best) || null;

      // Relative-minor protection: G/C/D often get heard as Em/Am/Bm if the root is weak.
      // If the relative major is nearly as good and has any root/bass support, take the major.
      if(best.suffix === 'm'){
        const relMajorRoot = normPc(best.root + 3);
        const relMajor = candidates.find(c => c.root === relMajorRoot && c.suffix === '');
        if(relMajor && relMajor.score >= best.score - 0.24){
          const minorReallyRooted = best.bassRoot >= 0.42 || best.rootBandRoot >= 0.46;
          const minorThirdClearlyWins = best.min3 >= best.maj3 * 1.25;
          const majorLooksReal = relMajor.maj3 >= 0.18 && relMajor.fifth >= 0.14 && (relMajor.rootE >= 0.16 || relMajor.bassRoot >= 0.16 || relMajor.rootBandRoot >= 0.16);
          if(majorLooksReal && (!minorReallyRooted || !minorThirdClearlyWins)) best = relMajor;
        }
      }

      // Major-vs-minor same root: require the third that defines quality.
      const isMinor = best.suffix === 'm';
      const thirdOk = isMinor
        ? (best.min3 >= 0.18 && best.min3 >= best.maj3 * 1.08)
        : (best.maj3 >= 0.18 && best.maj3 >= best.min3 * 0.88);
      if(!thirdOk) return null;

      if(best.weakest < 0.14) return null;
      if(best.need < 0.29 || best.score < 0.30 || best.rootE < 0.12 || best.fifth < 0.11) return null;

      // If another chord is extremely close and neither has root/bass authority, do not guess.
      second = candidates.find(c => c.label !== best.label) || null;
      const rootAuthority = Math.max(best.bassRoot || 0, best.rootBandRoot || 0, best.rootE || 0);
      if(second && second.score >= best.score - 0.045 && rootAuthority < 0.28) return null;

      const margin = second ? Math.max(0, best.score - second.score) : 0.20;
      const confidence = clamp01(
        best.score * 0.46 +
        best.need * 0.25 +
        best.weakest * 0.17 +
        Math.max(best.bassRoot, best.rootBandRoot) * 0.15 +
        margin * 0.90
      );
      if(confidence < cfg.chordMinConfidence) return null;
      return { type:'chord', value: cleanLabel(best.label), confidence, note: ROOTS[best.root], distinctStrong: agg.strongNotes.length, stable:false };
    }

    function inferNote(agg){
      if(!agg || !agg.strongNotes.length) return null;
      if(agg.strongNotes.length > 1) return null;
      const best = agg.strongNotes[0];
      const pitchPc = Number.isFinite(agg.pitchPc) ? agg.pitchPc : best.pc;
      if(best.v < 0.68 || agg.pitchConfidence < 0.34) return null;
      const value = pcName(pitchPc);
      const conf = clamp01(Math.max(best.v * 0.55, Number(agg.pitchConfidence) || 0));
      if(conf < cfg.noteMinConfidence) return null;
      return { type:'note', value, note:value, confidence: conf, distinctStrong: agg.strongNotes.length, stable:false };
    }

    function stabilize(det, nowMs){
      if(!det || !det.value){
        state.candidateKey = '';
        state.candidateSince = 0;
        state.candidateCount = 0;
        // Keep a recent lock very briefly so display does not flicker between attacks.
        if(state.locked && nowMs - (Number(state.lockedAt)||0) < 260) return state.locked;
        state.locked = null;
        return null;
      }
      const value = cleanLabel(det.value);
      const key = det.type + ':' + value;
      if(key === state.candidateKey){
        state.candidateCount += 1;
      }else{
        state.candidateKey = key;
        state.candidateSince = nowMs;
        state.candidateCount = 1;
      }
      const stableMs = nowMs - (Number(state.candidateSince) || nowMs);
      const neededMs = det.type === 'chord' ? cfg.chordStableMs : cfg.noteStableMs;
      const neededFrames = det.type === 'chord' ? 5 : 4;
      const sameLocked = state.locked && state.locked.type === det.type && state.locked.value === value;
      const veryConfident = Number(det.confidence)||0 > (det.type === 'chord' ? 0.66 : 0.60);
      if(sameLocked || veryConfident || (stableMs >= neededMs && state.candidateCount >= neededFrames)){
        const locked = { ...det, value, note: cleanLabel(det.note || value), stable:true };
        state.locked = locked;
        state.lockedAt = nowMs;
        return locked;
      }
      if(state.locked && nowMs - (Number(state.lockedAt)||0) < 220) return state.locked;
      return null;
    }

    function analyze(analyser, audioCtx, nowMs){
      const ctx = audioCtx || (analyser && analyser.context) || null;
      const sampleRate = ctx && ctx.sampleRate ? ctx.sampleRate : 48000;
      const t = Number(nowMs) || (typeof performance !== 'undefined' ? performance.now() : Date.now());
      const timeData = getTimeData(analyser);
      const level = rms(timeData);

      if(level < cfg.silenceRmsFloor || level < Math.max(cfg.silenceRmsFloor, state.noiseFloor * 1.28)){
        state.noiseFloor = Math.max(0.0022, Math.min(0.010, state.noiseFloor * 0.96 + level * 0.04));
        reset();
        return null;
      }
      state.noiseFloor = Math.max(0.0022, Math.min(0.012, state.noiseFloor * 0.995 + level * 0.005));

      const freqData = getFreqData(analyser);
      if(!freqData) return null;
      const peaks = pickSpectralPeaks(freqData, sampleRate, analyser.fftSize || 8192);
      const chromaPack = buildChromaFromPeaks(peaks);
      const pitch = detectSinglePitch(timeData, sampleRate, level);

      if(chromaPack || pitch){
        pushFrame({
          chroma: chromaPack && chromaPack.chroma,
          bass: chromaPack && chromaPack.bass,
          rootBand: chromaPack && chromaPack.rootBand,
          direct: chromaPack && chromaPack.direct,
          fundamental: chromaPack && chromaPack.fundamental,
          pitchPc: pitch ? pitch.pc : null,
          pitchConfidence: pitch ? pitch.confidence : 0,
          level
        }, t);
      }

      const agg = aggregate();
      if(!agg || agg.frameCount < 4) return null;
      let det = inferChord(agg) || inferNote(agg);
      state.lastDebug = agg ? {
        level,
        root: Number.isFinite(agg.likelyRootPc) ? ROOTS[agg.likelyRootPc] : '',
        bass: Number.isFinite(agg.likelyBassPc) ? ROOTS[agg.likelyBassPc] : '',
        notes: agg.chroma.map((v,i)=>ROOTS[i] + ':' + Number(v).toFixed(2)).join(' '),
        strong: agg.strongNotes.map(n=>ROOTS[n.pc]).join(','),
        det: det ? `${det.type}:${det.value}:${det.confidence.toFixed(2)}` : ''
      } : null;
      const stable = stabilize(det, t);
      state.lastResult = stable || det || null;
      return stable ? stable : (det ? { ...det, stable:false } : null);
    }

    function debug(){ return state.lastDebug; }

    return { analyze, reset, cleanLabel, debug };
  }

  window.SongRiderChordTracker = { create, cleanLabel };
})();
