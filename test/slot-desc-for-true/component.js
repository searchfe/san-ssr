
const san = require('san')

const Folder = san.defineComponent({
    template: '<div><h3 on-click="toggle"><slot name="title"/></h3><slot s-if="!hidden" s-for="i in repeat"/></div>',
    toggle: function () {
        const hidden = this.data.get('hidden')
        this.data.set('hidden', !hidden)
    },
    initData: function () {
        return { repeat: [1, 2] }
    }
})

const MyComponent = san.defineComponent({
    components: {
      'x-folder': Folder
    },

    template: '' +
        '<div>' +
          '<x-folder hidden="{{folderHidden}}"><b slot="title">{{name}}</b><p>{{desc}}</p></x-folder>' +
        '</div>'
})

exports = module.exports = MyComponent
